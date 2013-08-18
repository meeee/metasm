require_relative '../../utils'

module Metasm
  module CoreOpt::Optimizations
    module ConstantFolding
      module Operations
        include Metasm::CoreOpt::Utils

        # mov a, b
        # add a, c  => mov a, (b add c)
        def fold_instructions(flow, source_di, target_di, source_value)
          reg1 = source_di.instruction.args.first
          reg2 = target_di.instruction.args.first

          unless is_op(target_di, false, true) and
              (stack_vars_equal(reg1, reg2) or
                is_reg_alias?(reg1, reg2, :ignore_stack_vars => true))
            return :no_match
          end

          puts "    [-] Folding with reg_alias" if reg1.to_s != reg2.to_s
          begin
            res = solve_via_backtrace(source_di, target_di)
          rescue => e
            binding.pry
          end
          if is_reg(reg1)
            res2 = solve_arithm(target_di.instruction.opname,
                                source_di.instruction.args.last,
                                target_di.instruction.args.last,
                                reg1.sz)
          else
            res2 = "solve_arithm doens't work for stack vars"
          end

          if res and is_numeric(Expression[res])
            puts "    [-] Fold #{source_di} and  #{target_di} wih res : #{Expression[res]}"  if $VERBOSE
            if res != res2
              puts "      Fold results differ: Expected #{res2}, got #{res}"
            end
            if is_reg(reg1)
              $coreopt_stats[:const_fold_1] += 1 if reg1.to_s == reg2.to_s
              $coreopt_stats[:const_fold_1_alias] += 1 if reg1.to_s != reg2.to_s
            else
              $coreopt_stats[:const_fold_1_stack] += 1
            end
            source_di.instruction.args.pop
            source_di.instruction.args.push Expression[res]
            source_di.backtrace_binding = nil
            flow.burn_di(target_di)
            return :instruction_modified
          else
            puts "    [-] Fold failed with non-numeric res: #{res}"
          end
          return :condition_failed
        end

        # mov a, reg
        # sub a, reg => mov a, 0
        def fold_declaration_with_sub(flow, source_di, target_di, source_value)
          reg1 = source_di.instruction.args.first
          reg2 = target_di.instruction.args.first
          exp2 = target_di.instruction.args.last

          unless not is_decl(target_di) and
              is_reg(exp2) and
              reg1.to_s == reg2.to_s and
              exp2.to_s == source_di.instruction.args.last.to_s and
              target_di.instruction.opname == 'sub'
            return :no_match
          end

          puts "    [-] Fold(2) #{source_di} and  #{target_di} wih res : #{Expression[Expression[0]]}"  if $VERBOSE
          $coreopt_stats[:const_fold_2] += 1
          source_di.instruction.args.pop
          source_di.instruction.args.push Expression[0]
          flow.burn_di(target_di)
          return :instruction_modified
        end

      end
    end
  end
end
