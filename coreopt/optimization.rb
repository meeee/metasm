#
# This file extends Flow class and brings many optimizations that can be
# done on an instruction flow :
#     - peephole optimization
#     - constant_folding
#     - operation_folding
#     - stack_cleaning
#

class Flow

  # changed for x64
  Ia32Reg = [["rax", "al", "ax", "eax", "al", "ah"],
             ["rcx", "cl", "cx", "ecx", "cl", "ah"],
             ["rdx", "dl", "dx", "edx", "dl", "dh"],
             ["rbx", "bl", "bx", "ebx", "bl", "bh"],
             ["rsp", "spl", "sp", "esp"],
             ["rbp", "bpl", "bp", "ebp"],
             ["rsi", "sil", "si", "esi"],
             ["rdi", "dil", "di", "edi"],
             ["r8", "r8b", "r8w", "r8d"],
             ["r9", "r9b", "r9w", "r9d"],
             ["r10", "r10b", "r10w", "r10d"],
             ["r11", "r11b", "r11w", "r11d"],
             ["r12", "r12b", "r12w", "r12d"],
             ["r13", "r13b", "r13w", "r13d"],
             ["r14", "r14b", "r14w", "r14d"],
             ["r15", "r15b", "r15w", "r15d"]]

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
              $coreopt_stats[:stack_clean_burn_couple] += 1
              burn_di(di); burn_di(tdi)
              work_in_progress = true

            elsif not overwritten

              break if is_modrm(argSrc) and is_modrm(argDest)
              break if not argDest.sz == sz

              puts "     [-] Rewrite push-pop as mov : #{di} - #{tdi} " if $VERBOSE
              $coreopt_stats[:stack_clean_push_pop] += 1
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
            break if is_reg(argSrc) and write_access(tdi, argSrc)
            break if is_modrm(argSrc) and argSrc.b and is_reg(argSrc.b) and write_access(tdi, argSrc.b)
            break if is_modrm(argSrc) and argSrc.i and is_reg(argSrc.i) and write_access(tdi, argSrc.i)
          end

          overwritten = true if (is_reg(argSrc) and write_access(tdi, argSrc))
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

      imul_decl = is_imul_decl(di)
      if imul_decl
        # check whether next instruction reads carry or overflow flag set by imul
        # theoretically this might also happen later, so this can't catch all cases
        if read_access_flags(inext(di), [:eflag_o, :eflag_c])
          puts "Error: Instruction following imul reads carry/overflow flag"
          binding.pry
        end
        di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
        value = di.backtrace_binding[backtrace_write_key(di)].reduce
        di_before = di.to_s
        change_to_mov(di, value)
        puts "    [-] Replace.decl_imul #{di_before} with mov instruction: #{di}"
        $coreopt_stats[:const_prop_decl_imul] += 1

        work_in_progress = true
      end
      if is_decl_reg_or_stack_var(di) or imul_decl
        puts "decl: #{di}; stack var: #{is_stack_var(di.instruction.args.first)}"
        tdi = di
        reg1 = di.instruction.args.first
        if di.instruction.opname == 'xor'  # only is_decl for xor x, x
          exp1 = 0
        elsif imul_decl
          di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
          exp1 = di.backtrace_binding[backtrace_write_key(di)].reduce
        else
          exp1 = di.instruction.args.last
        end

        while tdi = inext(tdi)

          next if tdi.instruction.opname == 'nop'
          next if tdi.instruction.opname == 'test' and not is_reg(exp1)

          args2 = tdi.instruction.args

          # mov a, b      mov a, b
          # add c, a  =>  add c, b
          if (is_reg(reg1) and args2.length == 2 and is_reg(args2.last) and
          (args2.last.to_s == reg1.to_s or reg_alias(reg1.to_s).include? args2.last.to_s.to_sym)) and
          (not di.instruction.opname == 'lea') and (not tdi.instruction.opname == 'lea')
            # #and (tdi.instruction.args.last.sz == reg1.sz)

            # mov a, dword ptr [...]
            # xx dword ptr [...], a  => xx dword ptr [...], dword ptr [...] is
            # not supported
            # in IA32
            break if is_modrm(exp1) and is_modrm(args2.first)

            # pop a
            # mov b, a => useless replacement
            break if args2.last.to_s == exp1.to_s

            break if (not args2.last.sz == reg1.sz) and not is_numeric(exp1)
            break if di.instruction.opname == 'movzx'

            if tdi.instruction.opname == 'movsxd'
              prefix = "    [-] Replace.1_movsxd with mov and"
              $coreopt_stats[:const_prop_1_movsxd] += 1
            else
              prefix = "    [-] Replace.1"
              $coreopt_stats[:const_prop_1] += 1
            end
            $coreopt_stats[:const_prop_1_imul_decl] += 1 if imul_decl
            puts "#{prefix} #{Expression[args2.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE

            if tdi.instruction.opname == 'movsxd'
              # makes no sense to sign-extend a constant value, so sign-extend it here
              change_to_mov(tdi, solve_via_backtrace(di, tdi))
              raise 'Non-numeric result from propagation to movsxd: #{reuslt}' unless is_numeric(tdi.instruction.args.last)
            else
              args2.pop
              args2.push exp1
            end
            tdi.backtrace_binding = nil

            # mov a, b
            # mov b, a  => mov b, b is useless
            if tdi.instruction.opname == 'mov' and is_reg(args2.first) and
            is_reg(args2.last) and	(args2.first.to_s == args2.last.to_s)

              puts "    [-] NULL MOV in #{tdi}, instruction will burn in hell " if $VERBOSE
              $coreopt_stats[:const_prop_1_null_mov] += 1
              burn_di(tdi)
            end

            work_in_progress = true
            break

          # mov [rbp+a], b
          # add c, [rbp+a] => add c, b
          elsif (args2.length == 2 and stack_vars_equal(reg1, args2.last))
            break if di.instruction.opname == 'movzx'
            raise 'movsxd x, [stack var]' if di.instruction.opname == 'movsxd'

            puts "    [-] Replace.1_stack #{Expression[args2.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE
            $coreopt_stats[:const_prop_1_stack_var] += 1
            args2[1] = exp1
            tdi.backtrace_binding = nil

            # TODO DRY
            # mov a, b
            # mov b, a  => mov b, b is useless
            if tdi.instruction.opname == 'mov' and is_reg(args2.first) and
            is_reg(args2.last) and  (args2.first.to_s == args2.last.to_s)
              puts "    [-] NULL MOV in #{tdi}, instruction will burn in hell (stack var)" if $VERBOSE
              $coreopt_stats[:const_prop_1_null_mov] += 1
              burn_di(tdi)
            end

            work_in_progress = true
            break
          # mov a, b
          # imul c, a, imm => imul c, b, imm
          elsif (tdi.instruction.opname == 'imul' and args2.length == 3 and is_reg(args2[1]) and reg1.to_s == args2[1].to_s)
            puts "    [-] Replace.imul #{Expression[args2[1]]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE
            break if (not args2[1].sz == reg1.sz) and not is_numeric(exp1)
            args2[1] = exp1
            tdi.backtrace_binding = nil
            $coreopt_stats[:const_prop_imul] += 1
            work_in_progress = true
            break
            # mov a, 0x1234
            # mov b, dword ptr [a]
          elsif di.instruction.opname == 'mov' and is_modrm(tdi.instruction.args.last) and not is_modrm(exp1) and
          tdi.instruction.args.last.b.to_s == reg1.to_s

            work_in_progress = true
            puts "    [-] Replace.2 #{Expression[tdi.instruction.args.last]} in #{tdi} using #{Expression[exp1]} from #{di}" if $VERBOSE
            $coreopt_stats[:const_prop_2] += 1

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
            $coreopt_stats[:const_prop_3] += 1
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
            $coreopt_stats[:const_prop_4] += 1

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

          break if write_access(tdi, reg1)
          break if is_reg(exp1) and write_access(tdi, exp1)
          break if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b)
          break if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i)
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
          $coreopt_stats[:lea_replace_1] += 1

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
          $coreopt_stats[:lea_replace_2] += 1

          exp1.sz = tdi.instruction.args.first.sz if is_modrm(exp1) # keep size
          # of
          # indirection
          tdi.instruction.args[0] = exp1
          tdi.backtrace_binding = nil
          work_in_progress = true
          break

        end

        break if write_access(tdi, reg1)
        break if is_reg(exp1) and write_access(tdi, exp1)
        break if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b)
        break if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i)
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

      if is_decl_reg_or_stack_var(di) or is_op(di, true)
        stack_var = is_stack_var(di.instruction.args.first)
        puts "decl: #{di}; stack var: #{stack_var}"

        tdi = di
        reg = di.instruction.args.first
        exp1 = di.instruction.args.last
        used = false
        overwritten = false

        while tdi = inext(tdi)
          next if tdi.instruction.opname == 'nop'

          # Instructions like "pop cx" exhibit a read access to ecx due binding
          # encoding issue in encoding on an alias register.
          (used = true ; break) if read_access(tdi, reg) and ! (tdi.instruction.opname == 'pop' and is_reg(tdi.instruction.args.first) and not reg.to_s == 'esp')
          (overwritten = true ; break) if write_access(tdi, reg)
        end

        if not used and (overwritten or Semanticless_registers.include? reg.to_s) and is_stack_safe(di)
          puts "    [-] Deleting #{di} as unused definition (stack var: #{stack_var and true})" if $VERBOSE
          stat_key = (stack_var ? :decl_clean_delete_stack : :decl_clean_delete_reg)
          $coreopt_stats[stat_key] += 1
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

      if is_decl_reg_or_stack_var(di)
        puts "decl: #{di}; stack var: #{is_stack_var(di.instruction.args.first)}"
        tdi = di
        reg1 = di.instruction.args.first
        exp1 = di.instruction.args.last

        while tdi = inext(tdi)

          next if tdi.instruction.opname == 'nop'

          if write_access(tdi, reg1)

            op = tdi.instruction.opname
            reg2 = tdi.instruction.args.first
            exp2 = tdi.instruction.args.last

            # mov a, b
            # add a, c  => mov a, (b add c)
            if is_op(tdi, false, true) and (stack_vars_equal(reg1, reg2) or is_reg_alias?(reg1, reg2, :ignore_stack_vars => true))
              puts "    [-] Folding with reg_alias" if reg1.to_s != reg2.to_s
              begin
                res = solve_via_backtrace(di, tdi)
              rescue => e
                binding.pry
              end
              if is_reg(reg1)
                res2 = solve_arithm(op, exp1, exp2, reg1.sz)
              else
                res2 = "solve_arithm doens't work for stack vars"
              end

              if res and is_numeric(Expression[res])
                puts "    [-] Fold #{di} and  #{tdi} wih res : #{Expression[res]}"  if $VERBOSE
                if res != res2
                  puts "      Fold results differ: Expected #{res2}, got #{res}"
                end
                if is_reg(reg1)
                  $coreopt_stats[:const_fold_1] += 1 if reg1.to_s == reg2.to_s
                  $coreopt_stats[:const_fold_1_alias] += 1 if reg1.to_s != reg2.to_s
                else
                  $coreopt_stats[:const_fold_1_stack] += 1
                end
                di.instruction.args.pop
                di.instruction.args.push Expression[res]
                di.backtrace_binding = nil
                burn_di(tdi)
                work_in_progress = true
              else
                puts "    [-] Fold failed with non-numeric res: #{res}"
              end
            # elsif is_op(tdi, false, false) and is_reg_alias?(reg1, reg2)

              # mov a, reg
              # sub a, reg => mov a, 0
            elsif not is_decl(tdi) and is_reg(exp2)and reg1.to_s == reg2.to_s and exp2.to_s == exp1.to_s and tdi.instruction.opname == 'sub'
              puts "    [-] Fold(2) #{di} and  #{tdi} wih res : #{Expression[Expression[0]]}"  if $VERBOSE
              $coreopt_stats[:const_fold_2] += 1
              di.instruction.args.pop
              di.instruction.args.push Expression[0]
              burn_di(tdi)
              work_in_progress = true
            end

            break
          end

          break if read_access(tdi, reg1)
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
                $coreopt_stats[:op_fold_not_burn] += 1
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
                  $coreopt_stats[:op_fold_rolror_burn] += 1
                  burn_di(di)
                  burn_di(tdi)
                else
                  puts "    [-]  Fold rol/ror operations #{di} and  #{tdi}" if $VERBOSE
                  $coreopt_stats[:op_fold_rolror] += 1
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
                    $coreopt_stats[:op_fold_arithm_burn] += 1
                    burn_di(di)
                    burn_di(tdi)
                  else
                    puts "    [-] Fold operation #{di} and  #{tdi} wih res : #{Expression[res]}" if $VERBOSE
                    $coreopt_stats[:op_fold_arithm] += 1
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

          break if read_access(tdi, reg) and (not op_asso[op1] or (op_asso[op1] and ! (op_asso[op1].include? op2)))
          break if is_reg(reg) and write_access(tdi, reg)
        end

      end
    }

    purge_burnt!
    work_in_progress
  end

  def backtrace_write_key(di)
    op1 = di.instruction.args.first
    if is_reg(op1)
      # backtrace binding always uses 64-bit registers
      backtrace_write_key = reg_alias(op1).first
    else
      # stack var
     di.backtrace_binding.keys.find { |k| k.kind_of? Indirection }
    end
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

  def change_to_mov(di, value)
    args = di.instruction.args
    # remove all except target register
    (args.size - 1).times { args.pop }
    args.push(Expression[value])
    di.instruction.opname = 'mov'
    di.opcode = di.instruction.cpu.opcode_list.find { |op| op.name == 'mov' }
    di.backtrace_binding = nil
  end

  # is_decl : ensure that instruction (actually the DecodedIntruction) is a
  # declaration (or assigment)
  # mov, movzx, lea, pop, and lods instructions only are considered
  def is_decl(di)
    return (is_decl_reg_or_stack_var(di) and is_reg(di.instruction.args.first))
  end

  def is_decl_reg_or_stack_var(di)
    const = []
    args = di.instruction.args
    if (((['mov', 'movzx', 'lodsb', 'lea', 'pop'] .include? di.instruction.opname) or
        (di.instruction.opname == 'xor' and args.first == args.last)) and
        (is_reg(args.first) or is_stack_var(args.first)))  # XORing a reg with itself always results in 0

      b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
      const = b.select{|e, val| e and val and not e.to_s.match('eflag') }
    end
    not const.empty?
  end

  def is_imul_decl(di)
    args = di.instruction.args
    return (di.instruction.opname == 'imul' and args.size == 3 and
            is_numeric(args[1]) and is_numeric(args[2]))
  end

  # is_op : match following instruction types:
  # op reg, imm  (op reg, xx when weak def is set)
  # op reg
  def is_op(di, weak_def = false, stack_var_allowed = false)
    return false if not ['add', 'sub', 'or', 'xor', 'and', 'pxor', 'adc', 'sbb', 'inc', 'dec', 'not', 'neg', 'sar', 'shr', 'shl',  'rol', 'ror'].include? di.instruction.opname
    args = di.instruction.args
    reg_or_stack_var = (is_reg(args.first) or (stack_var_allowed and is_stack_var(args.first)))
    case args.length
    when 2
      return (reg_or_stack_var and (weak_def ? true : is_numeric(args.last)))

    when 1
      return reg_or_stack_var

    else return false
    end
  end

  # is_numeric : ensure that arg is a numeral
  def is_numeric(arg)
    return ((arg.kind_of? Integer) or
            (arg.kind_of? Expression and arg.reduce_rec.kind_of? Integer))
  end

  # is_modrm : ensure that arg is a modrm : [esp+4], etc.
  def is_modrm(arg)
    return (arg and arg.kind_of? Ia32::ModRM)
  end

  # is_reg : ensure that arg is a register
  def is_reg(arg)
    # FIXME implement RIP-relative addressing
    return (arg and arg.kind_of? Ia32::Reg and arg.symbolic != :rip)
  end

  def is_stack_var(arg)
    if arg.kind_of? Ia32::ModRM
      arg = arg.symbolic
    end
    return false unless arg.kind_of? Indirection
    return (arg.externals.size == 1 and arg.externals & [:rbp, :ebp])
  end

  # is_stack_safe : ensure that instruction does not interact with the stack
  def is_stack_safe(di)
    return (!write_access(di, di.instruction.cpu.str_to_reg('esp')) and
            !write_access(di, di.instruction.cpu.str_to_reg('rsp')))
  end

  # is_imune : ensure that a subflow (a list of instructions) does not overwrite
  # a
  # target (register)
  # FIXME doesn't work with modified write_access
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
    puts " [-] Test read/write access for #{reg} at in #{di}" if $DEBUG
    (write_access(di, reg_sym) | read_access(di, reg_sym))
  end

  # read_access : compute read access to a register/stack var
  # return boolean if access
  def read_access(di, var)
    puts " [-] Test  read access for #{var} at in #{di}" if $DEBUG

    b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)

    if is_stack_var(var)
      result = b.find do |target, source|
        if source.externals.include?(:rbp)
          stack_vars_equal(var, source.lexpr) or \
            stack_vars_equal(var, source.rexpr)
        else
          # puts "    read_access: No :rbp or nil lexpr/op: #{di}"
          false
        end
      end
      return (not result.nil?)
    else
      op1 = di.instruction.args.first
      op2 = di.instruction.args.last

      # due to binding encoding specificities (mask for non 32bits alias register,
      # aka,
      # ax, al, bc etc.)
      # a particular attention should be taken when automatically extracting
      # register
      # access from binding.
      if di.instruction.opname == 'movzx' or
          (di.instruction.opname == 'mov' and is_reg(op1) and (op1.sz != 32) and is_alias(op1, var))
        return true if (is_reg(op2) and is_alias(op2, var))
        return true if (op2.b and is_reg(op2.b) and is_alias(op2.b, var)) if is_modrm(op2)
        return true if (op2.i and is_reg(op2.i) and is_alias(op2.i, var)) if is_modrm(op2)
        return false
      end

      if di.instruction.opname =~ /cmov[a-zA-Z]*/
        return true if ((is_reg(op1) and is_alias(op1, var))) or ((is_reg(op2) and is_alias(op2, var)))
        return true if (op1.b and is_reg(op1.b) and is_alias(op1.b, var)) if is_modrm(op1)
        return true if (op1.i and is_reg(op1.i) and is_alias(op1.i, var)) if is_modrm(op1)
        return true if (op2.b and is_reg(op2.b) and is_alias(op2.b, var)) if is_modrm(op2)
        return true if (op2.i and is_reg(op2.i) and is_alias(op2.i, var)) if is_modrm(op2)
        return false
      end
      reg_sym = reg_alias(var)

      rd = (b.keys.grep(Indirection) + b.keys.grep(Expression)).map { |e| Expression[e].expr_indirections.map{|ind| ind.target} }.flatten
      rd += b.values

      ! (rd.map{|effect| Expression[effect].externals}.flatten & reg_sym).empty?
    end
  end

  def read_access_flags(di, flags)
    di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
    externals = di.backtrace_binding.values.map {|expr| expr.externals}.flatten
    return (not (externals & flags).empty?)
  end

  # write_access : compute write access to a register/stack var
  # return boolean if access
  def write_access(di, var)
    puts " [-] Test write access for #{var} at in #{di}" if $DEBUG

    begin
      b = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
    rescue
      raise 'I see a red door and I want i painted black'
    end

    if is_stack_var(var)
      return write_access_stack_var(di, var)
    end
    reg_sym = reg_alias(var)

    b.each{|k, v| puts "#{Expression[k]} => #{Expression[v]}"} if $DEBUG

    ! (b.keys.map{|effect| Expression[effect].externals}.flatten & reg_sym).empty?
  end

  def write_access_stack_var(di, var)
    binding = di.backtrace_binding ||= di.instruction.cpu.get_backtrace_binding(di)
    write_effect = binding.keys.find do |effect|
      unless effect.kind_of? Indirection and is_stack_var(effect)
        # puts " [-] No indirection, ignored: #{Expression[effect]}" if $VERBOSE
        return false
      end

      # effect_offset = effect.target.reduce.rexpr
      # var_offset = var.symbolic.target.reduce.rexpr
      # if effect_offset == var_offset
      if stack_vars_equal(effect, var)
        # puts "     Write access found: #{di} (#{Expression[effect]})" if $VERBOSE
        true
      else
        # puts "     No write access found: #{Expression[effect]}" if $VERBOSE
        false
      end
    end
    return (not write_effect.nil?)
  end

  def stack_vars_equal(var1, var2)
    unless is_stack_var(var1) and is_stack_var(var2)
      return false
    end
    var1_offset, var2_offset = [var1, var2].map do |var|
     var = (var.kind_of? Ia32::ModRM) ? var.symbolic : var
     var.target.reduce.rexpr
   end
    if var1_offset == var2_offset
      # puts " [+] Stack vars are equal: #{var1} #{var2}" if $VERBOSE
      return true
    else
      # puts " [-] Stack vars are not equal: #{var1} #{var2}" if $VERBOSE
      return false
    end

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

  def is_reg_alias?(reg1, reg2, opts={})
    if opts[:ignore_stack_vars] and is_stack_var(reg1)
      return false
    end
    reg_alias(reg1).include?(reg2.to_s.to_sym)
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

  def solve_via_backtrace(first_di, second_di)
    expression = backtrace_write_key(second_di)
    first_di.backtrace_binding ||= first_di.instruction.cpu.get_backtrace_binding(first_di)
    second_di.backtrace_binding ||= second_di.instruction.cpu.get_backtrace_binding(second_di)
    Expression[second_di.backtrace_binding[expression].bind(first_di.backtrace_binding).reduce]
  end
end
