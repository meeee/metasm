module Metasm::CoreOpt
  module Utils
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
      rescue => e
        puts 'I see a red door and I want i painted black'
        binding.pry
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
end