require_relative 'utils'
#
# This file extends Flow class and brings many optimizations that can be
# done on an instruction flow :
#     - peephole optimization
#     - constant_folding
#     - operation_folding
#     - stack_cleaning
#

module Metasm
  module CoreOpt
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

      # def constant_propagation
      #   (ConstantPropagator.new).constant_propagation
      #   raise "FIXME Load me from optimizations/constant_propagation.rb"
      # end

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
end