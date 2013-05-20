#
# This file extends Flow class and brings many optimizations that can be
# done on an instruction flow :
#     - peephole optimization
#     - constant_folding
#     - operation_folding
#     - stack_cleaning
#

class Flow

  Ia32Reg = [
    ['eax', 'ax', 'ah', 'al'],
    ['ecx', 'cx', 'ch', 'cl'],
    ['edx', 'dx', 'dh', 'dl'],
    ['ebx', 'bx', 'bh', 'bl'],
    ['esp', 'sp'],
    ['ebp', 'bp'],
    ['esi', 'si'],
    ['edi', 'di'],
  ]

  # target specific implementation
  def peephole
    nil
  end

  # stack_cleaning : recursively try to clean the stack by matching simple
  # useless
  # push-pop patterns
  def stack_cleaning(index = 0)
    puts "\n * stack cleaning *" if index == 0 and $VERBOSE
    return false if self.empty?

    work_in_progress = false

    self[index..self.length].each{|di|
      next if di.instruction.opname == 'nop'

      if di.instruction.opname == 'push' or di.instruction.opname == 'push.i16'

        argSrc = di.instruction.args.first
        sz = 32
        sz = 16 if (di.instruction.opname == 'push.i16') or ( (is_reg(argSrc)or is_modrm(argSrc)) and argSrc.sz == 16)
        tdi = di
        overwritten = false

        while tdi = inext(tdi)
          next if tdi.instruction.opname == 'nop'

          if tdi.instruction.opname == 'pop'

            argDest = tdi.instruction.args.first

            if is_reg(argSrc) and is_reg(argDest) and argSrc.to_s == argDest.to_s	and argDest.sz == sz
              puts "     [-] Burn couple : #{di} - #{tdi}" if $VERBOSE
              burn_di(di); burn_di(tdi)
              work_in_progress = true

            elsif not overwritten

              break if is_modrm(argSrc) and is_modrm(argDest)
              break if not argDest.sz == sz

              puts "     [-] Rewrite push-pop as mov : #{di} - #{tdi} " if $VERBOSE
              tdi.opcode = tdi.instruction.cpu.opcode_list.find{ |op| op.name == 'mov' and op.args == [:reg, :modrm] }
              tdi.instruction.opname = tdi.opcode.name
              tdi.instruction.args = [argDest, argSrc]

              if argDest.to_s == argSrc.to_s
                puts "       * NULL MOV in #{tdi}, instruction will burn in hell " if $VERBOSE
                burn_di(tdi)
              else
                tdi.add_comment('tweak stack clean rewrite')
                tdi.backtrace_binding = nil
              end

              burn_di(di)
              work_in_progress = true
            end

            break

          elsif tdi.instruction.opname == 'push' or  di.instruction.opname == 'push.i16'
            break if not stack_cleaning(self.index(tdi))
            work_in_progress = true
            tdi = di

          else
            break if is_reg(argSrc) and write_access(tdi, argSrc.to_s)
            break if is_modrm(argSrc) and argSrc.b and is_reg(argSrc.b) and write_access(tdi, argSrc.b.to_s)
            break if is_modrm(argSrc) and argSrc.i and is_reg(argSrc.i) and write_access(tdi, argSrc.i.to_s)
          end

          overwritten = true if (is_reg(argSrc) and write_access(tdi, argSrc.to_s))
        end

        break if (index != 0)
      end
    }

    purge_burnt! if index == 0
    work_in_progress
  end

  def constant_propagation()
    puts "\n * constant propagation *" if $VERBOSE

    work_in_progress = false
    return work_in_progress if self.empty?

    self.each{|di|
      next if di.instruction.opname == 'nop'
      next if di.instruction.opname == 'lea'

      if is_decl(di)

        tdi = di
        reg1 = di.instruction.args.first
        exp1 = di.instruction.args.last

        while tdi = inext(tdi)

          next if tdi.instruction.opname == 'nop'
          next if tdi.instruction.opname == 'test' and not is_reg(exp1)

          # mov a, b      mov a, b
          # add c, a  =>  add c, b
          if (tdi.instruction.args.length == 2 and is_reg(tdi.instruction.args.last) and
          (tdi.instruction.args.last.to_s == reg1.to_s or reg_alias(reg1.to_s).include? tdi.instruction.args.last.to_s.to_sym)) and
          (not di.instruction.opname == 'lea') and (not tdi.instruction.opname == 'lea')
            # #and (tdi.instruction.args.last.sz == reg1.sz)

            # mov a, dword ptr [...]
            # xx dword ptr [...], a  => xx dword ptr [...], dword ptr [...] is
            # not supported
            # in IA32
            break if is_modrm(exp1) and is_modrm(tdi.instruction.args.first)

            # pop a
            # mov b, a => useless replacement
            break if tdi.instruction.args.last.to_s == exp1.to_s

            break if (not tdi.instruction.args.last.sz == reg1.sz) and not is_numeric(exp1)
            break if di.instruction.opname == 'movzx'

            puts "    [-] Replace.1 #{Expression[tdi.instruction.args.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE

            tdi.instruction.args.pop
            tdi.instruction.args.push exp1
            tdi.backtrace_binding = nil

            # mov a, b
            # mov b, a  => mov b, b is useless
            if tdi.instruction.opname == 'mov' and is_reg(tdi.instruction.args.first) and
            is_reg(tdi.instruction.args.last) and	(tdi.instruction.args.first.to_s == tdi.instruction.args.last.to_s)

              puts "    [-] NULL MOV in #{tdi}, instruction will burn in hell " if $VERBOSE
              burn_di(tdi)
            end

            work_in_progress = true
            break

            # mov a, 0x1234
            # mov b, dword ptr [a]
          elsif di.instruction.opname == 'mov' and is_modrm(tdi.instruction.args.last) and not is_modrm(exp1) and
          tdi.instruction.args.last.b.to_s == reg1.to_s

            work_in_progress = true
            puts "    [-] Replace.2 #{Expression[tdi.instruction.args.last]} in #{tdi} using #{Expression[exp1]} from #{di}" if $VERBOSE

            case Expression[exp1].reduce_rec
            when Ia32::Reg
              tdi.instruction.args.last.b = exp1
              tdi.backtrace_binding = nil
            when Integer
              tdi.instruction.args.last.b = nil
              tdi.instruction.args.last.imm = exp1
              tdi.backtrace_binding = nil
            else
              work_in_progress = false
            end

            break

            # mov a, b			mov a, b
            # mov [a], c => mov [b], c
          elsif di.instruction.opname == 'mov' and is_reg(reg1) and is_reg(exp1) and
          is_modrm(tdi.instruction.args.first) and tdi.instruction.args.first.b.to_s == reg1.to_s

            break if tdi.instruction.args.first.b.to_s == exp1.to_s
            puts "    [-] Replace.3 #{Expression[tdi.instruction.args.first.b]} in #{tdi} using #{Expression[exp1]} from #{di}" if $VERBOSE
            tdi.instruction.args.first.b = exp1
            tdi.backtrace_binding = nil
            work_in_progress = true
            break

            # mov a, b 			mov a, b         or     mov a, b      mov a, b
            # push a    =>  push b                  pop [a]  =>  pop [b]
          elsif di.instruction.opname == 'mov' and (tdi.instruction.opname == 'push') and tdi.instruction.args.length == 1 and
          ((is_reg(tdi.instruction.args.first) and tdi.instruction.args.first.to_s == reg1.to_s) or
          (is_modrm(tdi.instruction.args.first) and tdi.instruction.args.first.b.to_s == reg1.to_s))

            puts "    [-] Replace.4 #{Expression[tdi.instruction.args.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE

            if is_modrm(tdi.instruction.args.first)

              work_in_progress = true

              case Expression[exp1].reduce_rec
              when Ia32::Reg
                tdi.instruction.args.first.b = exp1 if is_reg(exp1)
              when Integer
                tdi.instruction.args.first.b = nil
                tdi.instruction.args.first.imm = exp1
              else
                work_in_progress = false
              end

            else

              break if di.instruction.opname == 'movzx'
              tdi.instruction.args.pop
              tdi.instruction.args.push exp1
            end

            tdi.backtrace_binding = nil
            break

          end

          break if write_access(tdi, reg1.to_s)
          break if is_reg(exp1) and write_access(tdi, exp1.to_s)
          break if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b.to_s)
          break if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i.to_s)
        end

      end
    }

    purge_burnt!
    work_in_progress
  end

  # constant_propagation : propagate constant
  #
  # mov a, b      mov a, b
  # add c, a  =>  add c, b
  def lea_propagation
    puts "\n * lea propagation *" if $VERBOSE

    work_in_progress = false
    return work_in_progress if self.empty?

    self.each{|di|
      next if not di.instruction.opname == 'lea'

      tdi = di
      reg1 = di.instruction.args.first
      exp1 = di.instruction.args.last

      while tdi = inext(tdi)
        next if tdi.instruction.opname == 'nop'
        next if tdi.instruction.opname == 'test' and not is_reg(exp1)

        # lea a, dword ptr [b+c]
        # mov d, dword ptr [a]      => mov d, dword ptr [b+c]
        if is_modrm(tdi.instruction.args.last) and 	is_modrm(exp1) and
        tdi.instruction.args.last.b.to_s == di.instruction.args.first.to_s

          puts "    [-] LEA Replace.1 #{Expression[tdi.instruction.args.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE

          modrm = tdi.instruction.args.last
          reg2 = tdi.instruction.args.last.b

          break if not modrm.sz == 32

          tdi.instruction.args.pop

          exp1 = exp1.dup
          exp1.sz = modrm.sz
          tdi.instruction.args.push exp1

          burn_di(di)
          tdi.backtrace_binding = nil
          work_in_progress = true
          break

          # lea a, b 							lea a, b
          # mov dword ptr [a], c   =>  mov b, c
        elsif is_modrm(tdi.instruction.args.first) and is_reg(reg1) and tdi.instruction.args.first.b.to_s == reg1.to_s

          puts "    [-] LEA Replace.2 #{Expression[tdi.instruction.args.last]} in #{tdi} by its definition #{Expression[exp1]}" if $VERBOSE

          exp1.sz = tdi.instruction.args.first.sz if is_modrm(exp1) # keep size
          # of
          # indirection
          tdi.instruction.args[0] = exp1
          tdi.backtrace_binding = nil
          work_in_progress = true
          break

        end

        break if write_access(tdi, reg1.to_s)
        break if is_reg(exp1) and write_access(tdi, exp1.to_s)
        break if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b.to_s)
        break if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i.to_s)
      end

    }

    purge_burnt!
    work_in_progress
  end

  # list of registers that can be removed if not used in the Flow
  # eg mov ecx, 0 ; ret -> can discard the mov if Semanticless_registers = ['ecx']
  Semanticless_registers = []

  # decl_cleaning : delete unused declaration/assignment
  #
  # mov a, b
  # mov a, c   =>  mov a, c
  def decl_cleaning
    puts "\n * declaration cleaning *" if $VERBOSE

    work_in_progress = false
    return work_in_progress if self.empty?

    self.each{|di|
      next if di.instruction.opname == 'nop'

      if is_decl(di) or is_op(di, true)

        tdi = di
        reg = di.instruction.args.first
        exp1 = di.instruction.args.last
        used = false
        overwritten = false

        while tdi = inext(tdi)
          next if tdi.instruction.opname == 'nop'

          # Instructions like "pop cx" exhibit a read access to ecx due binding
          # encoding issue in encoding on an alias register.
          (used = true ; break) if read_access(tdi, reg.to_s) and ! (tdi.instruction.opname == 'pop' and is_reg(tdi.instruction.args.first) and not reg.to_s == 'esp')
          (overwritten = true ; break) if write_access(tdi, reg.to_s)
        end

        if not used and (overwritten or Semanticless_registers.include? reg.to_s) and is_stack_safe(di)
          puts "    [-] Deleting #{di} as unused definition" if $VERBOSE
          burn_di(di)
          work_in_progress = true
        end

      end
    }

    purge_burnt!
    work_in_progress
  end

  # constant_folding : fold two constants by solving their arithmetic
  #
  # mov a, b
  # add a, c  => mov a, (b add c)
  def constant_folding
    puts "\n * constant folding *" if $VERBOSE

    work_in_progress = false
    return work_in_progress if self.empty?

    self.each{|di|
      next if di.instruction.opname == 'nop'

      if is_decl(di)

        tdi = di
        reg1 = di.instruction.args.first
        exp1 = di.instruction.args.last

        while tdi = inext(tdi)

          next if tdi.instruction.opname == 'nop'

          if write_access(tdi, reg1.to_s)

            op = tdi.instruction.opname
            reg2 = tdi.instruction.args.first
            exp2 = tdi.instruction.args.last

            # mov a, b
            # add a, c  => mov a, (b add c)
            if is_op(tdi) and reg1.to_s == reg2.to_s

              res = solve_arithm(op, exp1, exp2, reg1.sz)

              if res and is_numeric(Expression[res])
                puts "    [-] Fold #{di} and  #{tdi} wih res : #{Expression[res]}"  if $VERBOSE
                di.instruction.args.pop
                di.instruction.args.push Expression[res]
                di.backtrace_binding = nil
                burn_di(tdi)
                work_in_progress = true
              end

              # mov a, reg
              # sub a, reg => mov a, 0
            elsif not is_decl(tdi) and is_reg(exp2)and reg1.to_s == reg2.to_s and exp2.to_s == exp1.to_s and tdi.instruction.opname == 'sub'
              puts "    [-] Fold(2) #{di} and  #{tdi} wih res : #{Expression[Expression[0]]}"  if $VERBOSE
              di.instruction.args.pop
              di.instruction.args.push Expression[0]
              burn_di(tdi)
              work_in_progress = true
            end

            break
          end

          break if read_access(tdi, reg1.to_s)
        end

      end
    }

    purge_burnt!
    work_in_progress
  end

  # operation_folding : fold operations by solving their arithmetic
  #
  #		sub al, 2bh      sub al, 36
  #		pop edx          pop edx
  #		sub al, 38h =>
  def operation_folding
    puts "\n * operation folding *" if $VERBOSE
    return false if self.empty?

    # expression reduction rules
    op_rules={
      ['add', 'add'] => 'add', ['sub', 'sub'] => 'add',
      ['add', 'sub'] => 'sub', ['sub', 'add'] => 'sub',
      ['xor', 'xor'] => 'xor', ['not', 'not'] => 'xor',
      ['rol', 'rol'] => 'add', ['ror', 'ror'] => 'add',
      ['rol', 'ror'] => 'sub', ['ror', 'rol'] => 'sub',
    }

    # operator's associativity
    op_asso={
      'add' => ['add', 'sub'],
      'sub' => ['add', 'sub'],
      'xor' => ['xor'],
      'rol' => ['rol', 'ror'],
      'ror' => ['rol', 'ror']
    }

    work_in_progress = false
    self.each{|di|
      next if di.instruction.opname == 'nop'

      if not is_decl(di) and is_op(di)

        op1 = di.instruction.opname
        reg = di.instruction.args.first
        exp1 = di.instruction.args.last
        tdi = di

        next if reg.to_s == 'esp'

        while tdi = inext(tdi)
          next if di.instruction.opname == 'nop'

          op2 = tdi.instruction.opname

          if not is_decl(tdi) and is_op(tdi) and reg.to_s == tdi.instruction.args.first.to_s

            exp2 = tdi.instruction.args.last

            case [op1, op2]
            when  ['not', 'not']
              if exp1.to_s == exp2.to_s
                puts "    [-] Fold not operations #{di} and  #{tdi}, both have been burnt" if $VERBOSE
                burn_di(di)
                burn_di(tdi)
                work_in_progress = true
                break
              end

            when ['rol', 'ror'], ['ror', 'rol']

              if is_numeric(Expression[exp1]) and is_numeric(Expression[exp2])
                exp1 = Expression[exp1].reduce_rec
                exp2 = Expression[exp2].reduce_rec

                if exp1 == exp2
                  puts "    [-] Fold rol/ror operations #{di} and  #{tdi}, both have been burnt" if $VERBOSE
                  burn_di(di)
                  burn_di(tdi)
                else
                  puts "    [-]  Fold rol/ror operations #{di} and  #{tdi}" if $VERBOSE
                  di.instruction.args.pop
                  if exp2 > exp1
                    di.opcode = di.instruction.cpu.opcode_list.find { |op| op.name == tdi.opcode.name}
                    di.instruction.opname = di.opcode.name
                    di.instruction.args.push Expression[solve_arithm('sub', exp2, exp1, 5)]
                  else
                    di.instruction.args.push Expression[solve_arithm('sub', exp1, exp2, 5)]
                  end

                  di.backtrace_binding = nil
                  burn_di(tdi)
                end

                work_in_progress = true
                break
              end

            else

              if op_rules[[op1, op2]]

                size = (['rol', 'ror'].include? op1) ? 5 : reg.sz
                res = solve_arithm(op_rules[[op1, op2]], exp1, exp2, size)

                if res and is_numeric(Expression[res])

                  if Expression[res].reduce_rec == 0
                    puts "    [-] Fold operation #{di} and  #{tdi}, both have been burnt" if $VERBOSE
                    burn_di(di)
                    burn_di(tdi)
                  else
                    puts "    [-] Fold operation #{di} and  #{tdi} wih res : #{Expression[res]}" if $VERBOSE
                    di.instruction.args.pop
                    di.instruction.args.push Expression[res]
                    di.backtrace_binding = nil
                    burn_di(tdi)
                  end

                  work_in_progress = true
                  break
                end
              end
            end
          end

          break if read_access(tdi, reg.to_s) and (not op_asso[op1] or (op_asso[op1] and ! (op_asso[op1].include? op2)))
          break if is_reg(reg) and write_access(tdi, reg.to_s)
        end

      end
    }

    purge_burnt!
    work_in_progress
  end

  # hum TODO
  def build_def_use(di)
    puts "\n * lding *" if $VERBOSE
    return false if self.empty?

    tdi = di
    def_use = []

    while tdi = inext(di)

    end

    purge_burnt!
    work_in_progress
  end

  # is_decl : ensure that instruction (actually the DecodedIntruction) is a
  # declaration (or assigment)
  # mov, movzx, lea, pop, and lods instructions only are considered
  def is_decl(di)
    const = []
    if (['mov', 'movzx', 'lodsb', 'lea', 'pop'] .include? di.instruction.opname)  and is_reg(di.instruction.args.first)

      b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
      const = b.select{|e, val|	e and val and not e.to_s.match('eflag') }

    end
    not const.empty?
  end

  # is_op : match following instruction types:
  # op reg, imm  (op reg, xx when weak def is set)
  # op reg
  def is_op(di, weak_def = false)
    return false if not ['add', 'sub', 'or', 'xor', 'and', 'pxor', 'adc', 'sbb', 'inc', 'dec', 'not', 'neg', 'shr', 'shl',  'rol', 'ror'].include? di.instruction.opname
    case di.instruction.args.length
    when 2
      return (is_reg(di.instruction.args.first) and (weak_def ? true : is_numeric(di.instruction.args.last)))

    when 1
      return is_reg(di.instruction.args.first)

    else return false
    end
  end

  # is_numeric : ensure that arg is a numeral
  def is_numeric(arg)
    return (arg and arg.kind_of? Expression and arg.reduce_rec.kind_of? Integer)
  end

  # is_modrm : ensure that arg is a modrm : [esp+4], etc.
  def is_modrm(arg)
    return (arg and arg.kind_of? Ia32::ModRM)
  end

  # is_reg : ensure that arg is a register
  def is_reg(arg)
    return (arg and arg.kind_of? Ia32::Reg)
  end

  # is_stack_safe : ensure that instruction does not interact with the stack
  def is_stack_safe(di)
    return !write_access(di, 'esp')
  end

  # is_imune : ensure that a subflow (a list of instructions) does not overwrite
  # a
  # target (register)
  def is_imune(subflow, target)
    imune = true
    subflow.each{|di| imune = false if write_access(di, target)}
    imune
  end

  # is_alias: return true if reg1 is an alias over reg2
  def is_alias(reg1, reg2)
    return (reg_alias(reg1.to_s).include? reg2.to_s.to_sym)
  end

  # rw_access : compute read/write access to a register
  # return boolean if access
  def rw_access(di, reg_sym)
    puts " [-] Test read/write acces for #{reg} at in #{di}" if $DEBUG
    (write_access(di, reg_sym) | read_access(di, reg_sym))
  end

  # read_access : compute read access to a register
  # return boolean if access
  def read_access(di, reg)
    puts " [-] Test read acces for #{reg} at in #{di}" if $DEBUG

    # due to binding encoding specificities (mask for non 32bits alias register,
    # aka,
    # ax, al, bc etc.)
    # a particular attention should be taken when automatically extracting
    # register
    # access from binding.
    if di.instruction.opname == 'movzx' or
    (di.instruction.opname == 'mov' and is_reg(di.instruction.args.first) and
    (not di.instruction.args.first.sz == 32) and is_alias(di.instruction.args.first, reg))

      op1 = di.instruction.args.first
      op2 = di.instruction.args.last

      return true if (is_reg(op2) and is_alias(op2, reg))
      return true if (op2.b and is_reg(op2.b) and is_alias(op2.b, reg)) if is_modrm(op2)
      return true if (op2.i and is_reg(op2.i) and is_alias(op2.i, reg)) if is_modrm(op2)
      return false
    end

    if di.instruction.opname =~ /cmov[a-zA-Z]*/

      op1 = di.instruction.args.first
      op2 = di.instruction.args.last

      return true if ((is_reg(op1) and is_alias(op1, reg))) or ((is_reg(op2) and is_alias(op2, reg)))
      return true if (op1.b and is_reg(op1.b) and is_alias(op1.b, reg)) if is_modrm(op1)
      return true if (op1.i and is_reg(op1.i) and is_alias(op1.i, reg)) if is_modrm(op1)
      return true if (op2.b and is_reg(op2.b) and is_alias(op2.b, reg)) if is_modrm(op2)
      return true if (op2.i and is_reg(op2.i) and is_alias(op2.i, reg)) if is_modrm(op2)
      return false
    end

    reg_sym = reg_alias(reg)
    b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)

    rd = (b.keys.grep(Indirection) + b.keys.grep(Expression)).map { |e| Expression[e].expr_indirections.map{|ind| ind.target} }.flatten
    rd += b.values

    ! (rd.map{|effect| Expression[effect].externals}.flatten & reg_sym).empty?
  end

  # write_access : compute write access to a register
  # return boolean if access
  def write_access(di, reg)
    puts " [-] Test write acces for #{reg} at in #{di}" if $DEBUG
    reg_sym = reg_alias(reg)

    begin
      b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
    rescue
      raise 'I see a red door and I want i painted black'
    end

    b.each{|k, v| puts "#{Expression[k]} => #{Expression[v]}"} if $DEBUG

    ! (b.keys.map{|effect| Expression[effect].externals}.flatten & reg_sym).empty?
  end

  # reg_alias : return all possible alias for a given register. Aliasing
  # registers
  # are described in Ia32Reg constant
  def reg_alias(reg)
    reg = reg.to_s if reg.kind_of? Ia32::Reg
    puts "  [-] register aliasing for #{reg}" if $VERBOSE and $DEBUG
    reg_alias = Ia32Reg.select{|regexpr| regexpr.include? reg}
    raise "Hazardous reg #{reg} - #{reg_alias}" if not reg_alias or reg_alias.length != 1
    reg_alias.pop.collect{|reg_str| reg_str.to_sym}
  end

  # solve_arithm : solve arithmetic operations
  def solve_arithm(op, exp1, exp2, size)

    opsz = size
    mask = (1 << opsz)-1

    case op
    when 'add', 'sub', 'or', 'xor', 'and', 'pxor', 'adc', 'sbb'
      e_op = { 'add' => :+, 'sub' => :-, 'or' => :|, 'and' => :&, 'xor' => :^, 'pxor' => :^, 'adc' => :+, 'sbb' => :- }[op]
      ret = Expression[exp1, e_op, exp2]
      ret = Expression[ret, e_op, :eflag_c] if op == 'adc' or op == 'sbb'
      ret = Expression[ret.reduce] if not exp1.kind_of? Indirection

    when 'inc'; ret = Expression[exp1, :+, 1]
    when 'dec'; ret = Expression[exp1, :-, 1]
    when 'not'; ret = Expression[exp1, :^, mask]
    when 'neg'; ret=  Expression[:-, exp1]
    when 'shr'; ret = Expression[Expression[exp1, :&, mask], :>>, Expression[exp2, :%, [opsz, 32].max]]
    when 'shl'; ret = Expression[exp1,  :<<, Expression[exp2, :%, [opsz, 32].max]]
    when 'ror', 'rol'
      opsz = [opsz, 32].max
      exp2 = Expression[exp2, :%, opsz]
      exp2 = Expression[opsz, :-, exp2] if op == 'rol'
      ret = Expression[[[exp1, :>>, exp2], :|, [exp1, :<<, [opsz, :-, exp2]]], :&, mask]

    else ret = :unsolved
    end

    ret = Expression[ret, :&, mask].reduce if not ret == :unsolved
    ret
  end

end
