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
          return false if self.empty?

          work_in_progress = false

          self.each do |di|
            work_in_progress |= constant_propagation_starting_from(di)
          end

          purge_burnt!
          work_in_progress
        end

        def constant_propagation_starting_from(source_di)
          return false unless source_preconditions_satisfied?(source_di)
          # puts "decl: #{source_di}; stack var: #{is_stack_var(source_di.instruction.args.first)}"

          source_value = source_value_from_di(source_di)

          target_di = source_di
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
              return false
            end
          end
          false
        end

        def constant_propagate_between_instructions(source_di, target_di, source_value)
          return :no_match unless target_preconditions_satisfied?(source_di, target_di, source_value)

          operations.each do |operation|
            result = send(operation, source_di, target_di, source_value)
            return result if result != :no_match
          end

          return :condition_failed unless continue_propagation?(source_di, target_di, source_value)
        end

        #
        # Callbacks used by walker - these are for constant propagation
        #

        def source_preconditions_satisfied?(source_di)
          (not ['nop', 'lea'].include? source_di.instruction.opname) and
            is_decl_reg_or_stack_var(source_di)
        end

        def source_value_from_di(source_di)
          if source_di.instruction.opname == 'xor'
            # for XOR x, x - other xors are filtered by is_decl
            0
          else
            source_di.instruction.args.last
          end
        end

        def target_preconditions_satisfied?(source_di, target_di, source_value)
          !(
            target_di.instruction.opname == 'nop' or
            (target_di.instruction.opname == 'test' and not is_reg(source_value)))
        end

        def continue_propagation?(source_di, target_di, source_value)
          reg1 = source_di.instruction.args.first
          !(
            # target di writes to target memory location(reg1) of source di
            write_access(target_di, reg1) or
            # source_value is a register and target di writes to this register
            (is_reg(source_value) and
              write_access(target_di, source_value)) or
            # source_value is an offset and target di writes to base
            (is_modrm(source_value) and
              source_value.b and
              is_reg(source_value.b) and
              write_access(target_di, source_value.b)) or
            # source_value is an offset and target di writes to index
            (is_modrm(source_value) and
              source_value.i and
              is_reg(source_value.i) and
              write_access(target_di, source_value.i)))
        end

        def operations
          [:replace_imul_declaration,
           :propagate_register_value,
           :propagate_stack_variable_value,
           :propagate_register_value_to_imul,
           :propagate_register_to_indirection,
           :propagate_register_to_target_indirection,
           :propagate_register_to_push]
        end
      end
    end
  end
end
