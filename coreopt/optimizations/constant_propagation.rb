require_relative 'constant_propagation/operations'

module Metasm
  module CoreOpt
    module Optimizations
      class Optimizer

      end

      module ConstantPropagator # < Optimizer
        include Operations

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

        def constant_propagation_starting_from(di)
          return false if ['nop', 'lea'].include? di.instruction.opname

          work_in_progress = false

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
            case constant_propagate_between_instructions(di, tdi, exp1, imul_decl)
            when :instruction_modified
              # work_in_progress, go to next source instruction
              return true  # work_in_progress
            when :no_match
              # found nothing to change, try next target instruction
              next
            when :condition_failed
              # propagation condition failed, stop propagating this di
              return work_in_progress
            end
          end
          work_in_progress
        end

        def constant_propagate_between_instructions(di, tdi, exp1, imul_decl)
          reg1 = di.instruction.args.first
          args2 = tdi.instruction.args

          return :no_match if tdi.instruction.opname == 'nop'
          return :no_match if tdi.instruction.opname == 'test' and not is_reg(exp1)


          result = propagate_register_value(di, tdi, exp1, imul_decl)
          return result if result != :no_match

          result = propagate_stack_variable_value(di, tdi, exp1)
          return result if result != :no_match

          result = propagate_register_value_to_imul(di, tdi, exp1)
          return result if result != :no_match

          result = propagate_register_to_indirection(di, tdi, exp1)
          return result if result != :no_match

          result = propagate_register_to_target_indirection(di, tdi, exp1)
          return result if result != :no_match

          result = propagate_register_to_push(di, tdi, exp1)
          return result if result != :no_match

          return :condition_failed if write_access(tdi, reg1)
          return :condition_failed if is_reg(exp1) and write_access(tdi, exp1)
          return :condition_failed if is_modrm(exp1) and exp1.b and is_reg(exp1.b) and write_access(tdi, exp1.b)
          return :condition_failed if is_modrm(exp1) and exp1.i and is_reg(exp1.i) and write_access(tdi, exp1.i)
        end

      end
    end
  end
end
