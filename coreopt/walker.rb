module Metasm
  module CoreOpt
    class Walker
      def initialize(flows)
        @flows = flows
      end

      def walk(flow)
        puts "\n * #{self.class.name.split('::').last} *" if $VERBOSE
        return false if flow.empty?

        before_walk

        work_in_progress = false

        flow.each do |source_di|
          before_source_di(flow, source_di)
          @between_flows = false
          puts ' [+] normal propagation'
          work_in_progress |= constant_propagation_starting_from(flow, source_di) ||
                              walk_between_flows(flow, source_di)

          after_source_di(flow, source_di)
        end

        flow.purge_burnt!
        work_in_progress
      end

      def constant_propagation_starting_from(flow,
                                             source_di,
                                             same_flow=true,
                                             begin_with=source_di)
        return false unless source_preconditions_satisfied?(source_di, same_flow)
        puts "     constant propagating from #{source_di}"

        # puts "decl: #{source_di}; stack var: #{is_stack_var(source_di.instruction.args.first)}"

        source_value = source_value_from_di(source_di)

        target_di = begin_with
        while target_di = flow.inext(target_di)
          case constant_propagate_between_instructions(flow,
                                                       source_di,
                                                       target_di,
                                                       source_value,
                                                       same_flow)
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

      def constant_propagate_between_instructions(flow,
                                                  source_di,
                                                  target_di,
                                                  source_value,
                                                  same_flow)
        return :no_match unless target_preconditions_satisfied?(source_di,
                                                                target_di,
                                                                source_value,
                                                                same_flow)

        if run_operations?(source_di, target_di)
          operations.each do |operation|
            result = send(operation, flow, source_di, target_di, source_value)
            return result if result != :no_match
          end
        end

        return :condition_failed unless continue_propagation?(source_di,
                                                              target_di,
                                                              source_value,
                                                              same_flow)
      end

      def walk_between_flows(from_flow, source_di, flow_stack=[from_flow])
        flow_stack << from_flow
        depth = flow_stack.size
        @between_flows = true
        puts " [+] between flows depth: #{depth}" if depth > 1

        unless source_preconditions_satisfied?(source_di, false)
          # puts " [+] Not walking between flows from #{source_di}: " +
          #      "source condition not satisfied"
          flow_stack.pop
          return false
        end
        puts " [+] Walking between flows from #{source_di}"

        from_flow.to.each do |to_flow_address|
          next if to_flow_address.nil?

          to_flow_info = @flows[to_flow_address]
          if flow_stack.include? to_flow_info[:flow]
            puts "     Flow already processed: #{Expression[to_flow_info[:flow].address]}"
            next
          end

          propagation_conditions_satisfied = propagate_between_flows?(from_flow,
                                                                      to_flow_info,
                                                                      source_di)

          puts "     propagation conditions satisfied: #{propagation_conditions_satisfied}"
          unless propagation_conditions_satisfied
            flow_stack.pop
            return false
          end
          to_flow = to_flow_info[:flow]
          result = constant_propagation_starting_from(to_flow, source_di, false, to_flow.first)

          return true if result
          # Walk recursively, let's see how this works
          return true if walk_between_flows(to_flow, source_di, flow_stack)
        end
        flow_stack.pop
        false
      end

      def propagate_between_flows?(from_flow, to_flow_info, source_di)
        # number of flows leading to to_flow
        to_flow = to_flow_info[:flow]
        to_flow_incoming_count = to_flow_info[:from].length

        puts "     to flow: #{Expression[from_flow.address]} has " +
             "#{to_flow_incoming_count} incoming edges"

        return false if multiple_executions_with_write_access?(to_flow_info, source_di)
        # TODO cache results

        if to_flow_incoming_count == 0
          return false
        elsif to_flow_incoming_count == 1
          # continue propagation
          propagate = true
        elsif to_flow_incoming_count > 1
          # to_flow has more than one incoming edge, so we have to check whether
          # the other flows to_flow has edges from violate propagation conditions.
          # In that case, we'll have to abort propagation. Otherwise we can continue,
          # as if the other block wouldn't exist.
          propagate = true
          incoming_without_from_flow = to_flow_info[:from] - [from_flow.address]
          incoming_without_from_flow.each do |incoming|
            incoming_flow = @flows[incoming][:flow]
            if incoming_flow.from.length != 1
              puts "     Incoming flow has more than one incoming flow: " +
                   "#{Expression[incoming]}: #{incoming_flow.from.length}; stopping propagation"
              propagate = false
            else
              propagate &= check_propagation_conditions(incoming_flow, source_di)
            end
          end
        end
        propagate
      end

      # Don't propagate to a flow that is being executed multiple times
      # and writes a stack variable - on second execution, the value is
      # probably different than the now propagated constant
      def multiple_executions_with_write_access?(flow_info, source_di)
        flow = flow_info[:flow]
        if flow_info[:from_subfuncret]
          puts "     flow returned from called function"
          return false
        end
        execution_count = execution_count_for_flow(flow)

        if execution_count != 1
          puts "     flow executed #{execution_count} times"

          # only allow propagation to block executed multiple times if it doesn't write
          # the declared variable/register
          var = source_di.instruction.args.first
          return true unless flow.all? { |di| not write_access(di, var)}
        end

        puts "     flow executed #{execution_count} time(s). Propagating :)"
        false
      end

      def execution_count_for_flow(flow)
        comments = flow.first.comment
        if not comments.kind_of? Array
          puts '     to flow: no information about number of executions, not propagating.'
          require 'pry'; binding.pry
          return
        end

        matches = comments.map do |comment|
          comment.match(/\Aexecuted ([0-9]+) time(s?)\Z/)
          $1
        end.compact

        if matches.length != 1
          puts "     not exactly one execution comment found: #{matches.join(', ')}; " +
               "not propgating"
          require 'pry'; binding.pry

          return
        end

        matches.first.to_i
      end

      def check_propagation_conditions(incoming_flow, source_di)
        continue = true
        source_value = source_value_from_di(source_di)

        incoming_flow.each do |target_di|
          continue = continue_propagation?(source_di, target_di, source_value, false)
          break unless continue
        end
        continue
      end

      ##
      # Default no-op methods
      #
      def before_walk
      end

      def before_source_di(flow, source_di)
      end

      def source_preconditions_satisfied?(source_di, same_flow)
        source_di.instruction.opname != 'nop'
      end

      def source_value_from_di(source_di)
        nil
      end

      def target_preconditions_satisfied?(source_di, target_di, source_value, same_flow)
        target_di.instruction.opname != 'nop'
      end

      def run_operations?(source_di, target_di)
        true
      end

      def continue_propagation?(source_di, target_di, source_value, same_flow)
        true
      end

      def after_source_di(flow, source_di)
      end

      def operations(source_di)
        []
      end

    end
  end
end
