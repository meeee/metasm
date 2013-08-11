require_relative 'constant_propagation/operations'

module Metasm
  module CoreOpt
    module Optimizations
      class Optimizer

      end

      module ConstantPropagator # < Optimizer
        include Operations
        ##
        # Loops
        #

        def constant_propagation #(di, tdi)
          puts "\n * constant propagation *" if $VERBOSE

          work_in_progress = false
          return work_in_progress if self.empty?

          self.each do |di|
            work_in_progress |= constant_propagation_starting_from(di)
          end

          purge_burnt!
          work_in_progress
        end

        def constant_propagation_starting_from(source_di)
          return false if ['nop', 'lea'].include? source_di.instruction.opname

          work_in_progress = false

          return work_in_progress unless is_decl_reg_or_stack_var(source_di)
          # puts "decl: #{source_di}; stack var: #{is_stack_var(source_di.instruction.args.first)}"
          target_di = source_di
          reg1 = source_di.instruction.args.first
          if source_di.instruction.opname == 'xor'  # only is_decl for is xor x, x
            source_value = 0
          else
            source_value = source_di.instruction.args.last
          end

          while target_di = inext(target_di)
            case constant_propagate_between_instructions(source_di, target_di, source_value)
            when :instruction_modified
              # work_in_progress, go to next source instruction
              return true  # work_in_progress
            when :no_match
              # found nothing to change, try next target instruction
              next
            when :condition_failed
              # propagation condition failed, stop propagating this source_di
              return work_in_progress
            end
          end
          work_in_progress
        end

        def constant_propagate_between_instructions(di, tdi, exp1)
          reg1 = di.instruction.args.first
          args2 = tdi.instruction.args

          return :no_match if tdi.instruction.opname == 'nop'
          return :no_match if tdi.instruction.opname == 'test' and not is_reg(exp1)


          [:replace_imul_declaration,
           :propagate_register_value,
           :propagate_stack_variable_value,
           :propagate_register_value_to_imul,
           :propagate_register_to_indirection,
           :propagate_register_to_target_indirection,
           :propagate_register_to_push
          ].each do |operation|
            result = send(operation, di, tdi, exp1)
            return result if result != :no_match
          end

          return :condition_failed if write_access(tdi, reg1)
          return :condition_failed if is_reg(exp1) and write_access(tdi, exp1)
          return :condition_failed if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b)
          return :condition_failed if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i)
        end

      end
    end
  end
end
