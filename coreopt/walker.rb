module Metasm
  module CoreOpt
    class Walker
      def walk(flow)
        puts "\n * #{self.class.name.split('::').last} *" if $VERBOSE
        return false if flow.empty?

        work_in_progress = false

        flow.each do |di|
          work_in_progress |= constant_propagation_starting_from(flow, di)
        end

        flow.purge_burnt!
        work_in_progress
      end

      def constant_propagation_starting_from(flow, source_di)
        return false unless source_preconditions_satisfied?(source_di)
        # puts "decl: #{source_di}; stack var: #{is_stack_var(source_di.instruction.args.first)}"

        source_value = source_value_from_di(source_di)

        target_di = source_di
        while target_di = flow.inext(target_di)
          case constant_propagate_between_instructions(flow, source_di, target_di, source_value)
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

      def constant_propagate_between_instructions(flow, source_di, target_di, source_value)
        return :no_match unless target_preconditions_satisfied?(source_di, target_di, source_value)

        operations.each do |operation|
          result = send(operation, flow, source_di, target_di, source_value)
          return result if result != :no_match
        end

        return :condition_failed unless continue_propagation?(source_di, target_di, source_value)
      end
    end
  end
end
