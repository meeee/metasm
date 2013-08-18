require_relative '../walker'
require_relative 'constant_folding/operations'

module Metasm::CoreOpt
  module Optimizations
    class ConstantFolder < Walker
      include ConstantFolding::Operations

      def source_preconditions_satisfied?(source_di)
        super and is_decl_reg_or_stack_var(source_di)
      end

      def run_operations?(source_di, target_di)
        write_access(target_di, source_di.instruction.args.first)
      end

      def continue_propagation?(source_di, target_di, source_value)
        not read_access(target_di, source_di.instruction.args.first) and
          not write_access(target_di, source_di.instruction.args.first)
      end

      def operations
        [:fold_instructions,
         :fold_declaration_with_sub]
      end
    end
  end
end
