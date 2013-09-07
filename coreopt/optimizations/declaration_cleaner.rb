require_relative '../walker'

module Metasm::CoreOpt
  module Optimizations

    # DeclarationCleaner : delete unused declarations/assignments
    #
    # mov a, b
    # mov a, c   =>  mov a, c
    class DeclarationCleaner < Walker
      include Metasm::CoreOpt::Utils

      # list of registers that can be removed if not used in the Flow
      # eg mov ecx, 0 ; ret -> can discard the mov if SEMANTICLESS_REGISTERS = ['ecx']
      SEMANTICLESS_REGISTERS = []

      def before_source_di(flow, source_di)
        @used = false
        @overwritten = false
      end

      def after_source_di(flow, source_di)
        reg = source_di.instruction.args.first
        if not @used and
            (@overwritten or SEMANTICLESS_REGISTERS.include? reg.to_s) and
            is_stack_safe(source_di)

          stack_var = is_stack_var(source_di.instruction.args.first)
          puts "    [-] Deleting #{source_di} as unused definition (stack var: #{stack_var and true})" if $VERBOSE

          stat_key = (is_stack_var(reg) ? :decl_clean_delete_stack : :decl_clean_delete_reg)
          $coreopt_stats[stat_key] += 1

          flow.burn_di(source_di)
          work_in_progress = true
        end
      end

      def source_preconditions_satisfied?(source_di, same_flow)
        super and is_decl_reg_or_stack_var(source_di) or is_op(source_di, true) and same_flow
      end

      def continue_propagation?(source_di, target_di, source_value, same_flow)
        true
      end

      def operations
        [:check_for_access]
      end

      def check_for_access(flow, source_di, target_di, source_value)
        reg = source_di.instruction.args.first

        # Instructions like "pop cx" exhibit a read access to ecx due binding
        # encoding issue in encoding on an alias register.
        if read_access(target_di, reg) and
          ! (target_di.instruction.opname == 'pop' and
             is_reg(target_di.instruction.args.first) and not reg.to_s == 'esp')
          @used = true
          return :condition_failed
        end
        if write_access(target_di, reg)
          @overwritten = true
          return :condition_failed
        end
      end
    end
  end
end
