require_relative 'utils'
#
# This file extends Flow class and brings many optimizations that can be
# done on an instruction flow :
#     - peephole optimization
#     - constant_folding
#     - operation_folding
#     - stack_cleaning
#

module Metasm::CoreOpt
  class Flow
    include Metasm::CoreOpt::Utils

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
          # puts "decl: #{di}; stack var: #{is_stack_var(di.instruction.args.first)}"
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
                break if is_modrm(exp1)
                # makes no sense to sign-extend a constant value, so sign-extend it here
                change_to_mov(tdi, solve_via_backtrace(di, tdi))
                if not is_numeric(tdi.instruction.args.last)
                  puts "Error: Non-numeric result from propagation to movsxd: #{tdi.instruction.args.last}"
                  binding.pry
                end
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
              if tdi.instruction.opname == 'lea'
                $coreopt_stats[:const_prop_1_stack_var_lea] += 1
                change_to_mov(tdi, exp1)
              else
                $coreopt_stats[:const_prop_1_stack_var] += 1
                args2[1] = exp1
                tdi.backtrace_binding = nil
              end

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
            elsif (tdi.instruction.opname == 'imul' and args2.length == 3 and is_reg(args2[1]) and is_reg_alias?(reg1, args2[1],  :ignore_stack_vars => true))
              break if (not args2[1].sz == reg1.sz) and not is_numeric(exp1)
              break unless [32, 64].include?(reg1.sz) and [32, 64].include?(args2[1].sz)
              if is_numeric(exp1)
                exp1_masked = Expression[exp1, :&, ((1 << args2[1].sz) - 1)].reduce
              else
                exp1_masked = exp1
              end
              puts "    [-] Replace.imul #{Expression[args2[1]]} in #{tdi} by its definition #{Expression[exp1]} (masked: #{Expression[exp1_masked]}) from #{di}" if $VERBOSE
              args2[1] = exp1_masked
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
                args2.last.b = nil
                args2.last.imm = Expression[args2.last.imm, :+, exp1].reduce
                tdi.backtrace_binding = nil
                tdi.backtrace_binding ||= tdi.instruction.cpu.get_backtrace_binding(tdi)
                reduced = tdi.backtrace_binding[backtrace_write_key(tdi)].reduce
                if is_numeric(reduced)
                  change_to_mov(tdi, reduced)
                  puts "        Replace with mov: #{tdi}"
                end
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
          # puts "decl: #{di}; stack var: #{stack_var}"

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
          # puts "decl: #{di}; stack var: #{is_stack_var(di.instruction.args.first)}"
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
  end
end
