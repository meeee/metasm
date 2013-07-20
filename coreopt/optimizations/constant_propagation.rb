module Metasm
  module CoreOpt
    module Optimizations
      class Optimizer

      end

      module ConstantPropagator # < Optimizer
        def replace_imul_declaration(di)
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
        end

        def propagate_register_value(di, tdi, exp1, imul_decl)
          args2 = tdi.instruction.args
          if tdi.instruction.opname == 'movsxd'
            prefix = "    [-] Replace.1_movsxd with mov and"
            $coreopt_stats[:const_prop_1_movsxd] += 1
          else
            prefix = "    [-] Replace.1"
            $coreopt_stats[:const_prop_1] += 1
          end
          $coreopt_stats[:const_prop_1_imul_decl] += 1 if imul_decl
          puts "#{prefix} #{Expression[args2.last]} in #{tdi} by its " +
               "definition #{Expression[exp1]} from #{di}" if $VERBOSE

          if tdi.instruction.opname == 'movsxd'
            unless is_modrm(exp1)
              # makes no sense to sign-extend a constant value, so sign-extend it here
              change_to_mov(tdi, solve_via_backtrace(di, tdi))
              if not is_numeric(tdi.instruction.args.last)
                puts "Error: Non-numeric result from propagation to movsxd: #{tdi.instruction.args.last}"
                binding.pry
              end
            end
          else
            args2.pop
            args2.push exp1
          end
          tdi.backtrace_binding = nil

          # mov a, b
          # mov b, a  => mov b, b is useless
          if tdi.instruction.opname == 'mov' and is_reg(args2.first) and
          is_reg(args2.last) and  (args2.first.to_s == args2.last.to_s)

            puts "    [-] NULL MOV in #{tdi}, instruction will burn in hell " if $VERBOSE
            $coreopt_stats[:const_prop_1_null_mov] += 1
            burn_di(tdi)
          end
        end

        def propagate_stack_variable_value(di, tdi, exp1)
          raise 'movsxd x, [stack var]' if di.instruction.opname == 'movsxd'
          args2 = tdi.instruction.args
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
        end

        def propagate_register_value_to_imul(di, tdi, exp1)
          args2 = tdi.instruction.args
          if is_numeric(exp1)
            exp1_masked = Expression[exp1, :&, ((1 << args2[1].sz) - 1)].reduce
          else
            exp1_masked = exp1
          end
          puts "    [-] Replace.imul #{Expression[args2[1]]} in #{tdi} by its definition #{Expression[exp1]} (masked: #{Expression[exp1_masked]}) from #{di}" if $VERBOSE
          args2[1] = exp1_masked
          tdi.backtrace_binding = nil
          $coreopt_stats[:const_prop_imul] += 1
        end

        def propagate_register_to_indirection(source_di, target_di, exp1)
          target_args = target_di.instruction.args

          work_in_progress = true
          puts "    [-] Replace.2 #{Expression[target_di.instruction.args.last]}" +
               " in #{target_di} using #{Expression[exp1]} from #{source_di}" if $VERBOSE
          $coreopt_stats[:const_prop_2] += 1

          case Expression[exp1].reduce_rec
          when Ia32::Reg
            target_di.instruction.args.last.b = exp1
            target_di.backtrace_binding = nil
          when Integer
            target_args.last.b = nil
            target_args.last.imm = Expression[target_args.last.imm, :+, exp1].reduce
            target_di.backtrace_binding = nil
            target_di.backtrace_binding ||= target_di.instruction.cpu.get_backtrace_binding(target_di)
            reduced = target_di.backtrace_binding[backtrace_write_key(target_di)].reduce
            if is_numeric(reduced)
              change_to_mov(target_di, reduced)
              puts "        Replace with mov: #{target_di}"
            end
          else
            work_in_progress = false
          end
          return work_in_progress
        end

        def propagate_register_to_target_indirection(di, tdi, exp1)
          puts "    [-] Replace.3 #{Expression[tdi.instruction.args.first.b]} in #{tdi} using #{Expression[exp1]} from #{di}" if $VERBOSE
          $coreopt_stats[:const_prop_3] += 1
          tdi.instruction.args.first.b = exp1
          tdi.backtrace_binding = nil
        end

        def propagate_register_to_push(di, tdi, exp1)
          puts "    [-] Replace.4 #{Expression[tdi.instruction.args.last]} in #{tdi} by its definition #{Expression[exp1]} from #{di}" if $VERBOSE
          $coreopt_stats[:const_prop_4] += 1
          work_in_progress = false
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
            [work_in_progress, :next_inner] if di.instruction.opname == 'movzx'
            tdi.instruction.args.pop
            tdi.instruction.args.push exp1
          end

          tdi.backtrace_binding = nil
          return [work_in_progress, :next_inner]
        end

        def constant_propagation #(di, tdi)
          puts "\n * constant propagation *" if $VERBOSE

          work_in_progress = false
          return work_in_progress if self.empty?

          self.each do |di|
            work_in_progress = constant_propagation_starting_from(di, work_in_progress)
          end

          purge_burnt!
          work_in_progress
        end

        def constant_propagation_starting_from(di, work_in_progress)
          # return :next_outer if di.instruction.opname == 'nop'
          # return :next_outer if di.instruction.opname == 'lea'
          return work_in_progress if ['nop', 'lea'].include? di.instruction.opname

          imul_decl = is_imul_decl(di)
          if imul_decl
            replace_imul_declaration(di)
            work_in_progress = true
          end
          return work_in_progress unless is_decl_reg_or_stack_var(di) or imul_decl
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

              propagate_register_value(di, tdi, exp1, imul_decl)
              work_in_progress = true
              break
            # mov [rbp+a], b
            # add c, [rbp+a] => add c, b
            elsif (args2.length == 2 and stack_vars_equal(reg1, args2.last))
              break if di.instruction.opname == 'movzx'
              propagate_stack_variable_value(di, tdi, exp1)
              work_in_progress = true
              break
            # mov a, b
            # imul c, a, imm => imul c, b, imm
            elsif (tdi.instruction.opname == 'imul' and args2.length == 3 and is_reg(args2[1]) and is_reg_alias?(reg1, args2[1],  :ignore_stack_vars => true))
              break if (not args2[1].sz == reg1.sz) and not is_numeric(exp1)
              break unless [32, 64].include?(reg1.sz) and [32, 64].include?(args2[1].sz)
              propagate_register_value_to_imul(di, tdi, exp1)
              work_in_progress = true
              break
              # mov a, 0x1234
              # mov b, dword ptr [a]
            elsif di.instruction.opname == 'mov' and is_modrm(tdi.instruction.args.last) and not is_modrm(exp1) and
            tdi.instruction.args.last.b.to_s == reg1.to_s
              work_in_progress = propagate_register_to_indirection(di, tdi, exp1)
              break

              # mov a, b      mov a, b
              # mov [a], c => mov [b], c
            elsif di.instruction.opname == 'mov' and is_reg(reg1) and is_reg(exp1) and
            is_modrm(tdi.instruction.args.first) and tdi.instruction.args.first.b.to_s == reg1.to_s

              break if tdi.instruction.args.first.b.to_s == exp1.to_s
              propagate_register_to_target_indirection(di, tdi, exp1)
              work_in_progress = true
              break

              # mov a, b      mov a, b         or     mov a, b      mov a, b
              # push a    =>  push b                  pop [a]  =>  pop [b]
            elsif di.instruction.opname == 'mov' and (tdi.instruction.opname == 'push') and tdi.instruction.args.length == 1 and
            ((is_reg(tdi.instruction.args.first) and tdi.instruction.args.first.to_s == reg1.to_s) or
            (is_modrm(tdi.instruction.args.first) and tdi.instruction.args.first.b.to_s == reg1.to_s))
              work_in_progress, next_step = propagate_register_to_push(di, tdi, exp1)
              raise 'next_step != :next_inner' unless next_step == :next_inner
              break

            end

            break if write_access(tdi, reg1)
            break if is_reg(exp1) and write_access(tdi, exp1)
            break if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b)
            break if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i)
          end
          work_in_progress
        end

      end
    end
  end
end