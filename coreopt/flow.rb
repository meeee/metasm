require_relative 'optimizations'

module Metasm
  module CoreOpt

    class Flow < Array
      attr_accessor :block_addresses
      attr_accessor :original_last_address

      def initialize(disasm, content = nil)
        super()
        self.concat(content) if content
        @disasm = disasm
        @block_addresses = []
        @original_last_address = nil
      end

      def linear(flowB)

        self.clean!
        flowB.clean!

        # Lazy textual linear matching between two flows
        res = true
        if self.length == 0 and self.length != flowB.length
          res = false
        else
          self.each_index{ |i|
            if not self[i].kind_of?(Metasm::DecodedInstruction) or not flowB[i].kind_of?(Metasm::DecodedInstruction) or
            self[i].instruction.to_s.gsub('+0]', ']') != flowB[i].instruction.to_s.gsub('+0]', ']')
              res = false
              break
            end
          }
        end

        res
      end

      def clean!(flows)
        return self if self.empty?
        filter_jump!
        optimize!(flows)
        filter_jump!
        self
      end

      def optimize!(flows)
        return self if (self.empty?)

        pass = 0
        puts self if $VERBOSE

        # disabled:
        # * peephole
        # * stack_cleaning
        # * operation_folding
        declaration_cleaner = Optimizations::DeclarationCleaner.new(flows)
        constant_propagator = Optimizations::ConstantPropagator.new(flows)
        constant_folder = Optimizations::ConstantFolder.new(flows)

        while (declaration_cleaner.walk(self) |
               constant_propagator.walk(self) |
               constant_folder.walk(self))
          pass +=1
          if $VERBOSE
            puts "\n----- pass #{pass} -------\n"
            if $DEBUG
              self.each{|di| puts di}
              puts "\n---------\n"
            end
          end
        end

        purge_burnt!
        self
      end

      def filter_jump!
        self.each{|di|
          next if not di.kind_of?(Metasm::DecodedInstruction)

          if di.opcode.name == 'jmp' and di.instruction.args.first.kind_of?(Metasm::Expression) and
          @disasm.normalize(di.instruction.args.first).kind_of?(::Integer)

            burn_di(di)
          end
        }
        purge_burnt!
      end

      # burn_di : mark an instruction as burnt, backtrace_binding is also deleted. di will burn in hell with thousands of dirty-minded siners.
      def burn_di(di)
        di.instruction.opname = 'nop'
        di.backtrace_binding = nil
        next_di = inext(di)
        return if next_di.nil?
        next_di.comment ||= []
        unless di.comment.nil? || di.comment.size == 0
          next_di.comment += ['from prev: ', di.comment].flatten
        end
        if next_di.comment and not next_di.comment.empty?
          next_di.comment.map! {|c| (count = /^-([0-9]+)i$/.match(c) and
                                             "-#{count[1].to_i + 1}i") or c }
        else
          next_di.comment += ['-1i']
        end
      end

      # purge_burnt : remove instructions marked as burnt from the flow
      def purge_burnt!
        self.delete_if{|di| di.kind_of?(Metasm::DecodedInstruction) and
                            di.instruction.opname == 'nop' and
                            $coreopt_stats[:purged_instructions] += 1 and true}
      end

      def inext(di)
        (pos = self.index(di)) ? self[pos+1] : nil
      end

      def solve_ind(i)
        case i
        when Indirection
          p = solve_ind(i.target)
          if s = @disasm.get_section_at(p)
            s[0].decode_imm("a#{i.len*8}".to_sym, @disasm.cpu.endianness)
          else
            Expression::Unknown
          end

        when Expression; i.bind(i.expr_indirections.inject({}) { |b, e| b.update e => Expression[solve_ind(e)] }).reduce
        when :unknown; i
        else Expression::Unknown
        end
      end

      def insert_nop(nop)
        nop = nop.instruction.cpu.opcode_list.find { |op| op.name == 'nop'}
        nop.instruction.opname = push.opcode.name
        nop.instruction.args = []
        nop.backtrace_binding = nil
      end

      def pattern_search(pat)
        return false if self.empty?
        matched = false
        subFlow = nil

        self.each_index{ |i|
          if pat.length <= (self.length - i)
            subFlow = self[i, pat.length]
            (matched = true; break) if subFlow and pattern_match(pat, subFlow)
          end
        }

        subFlow = nil if not matched
        subFlow
      end

      def pattern_match(pat, flow)

        return false if pat.empty?
        str = flow.map{ |di| di.instruction.to_s }
        matches = []
        pat.zip(str).all? { |pt, st|
          next false if not st
          wantmatch = []
          pt = pt.gsub(/([%@])(\d)/) {
            type = $1
            i = $2.to_i
            if matches[i]; Regexp.escape(matches[i])
            else wantmatch << i ; { '%' => '(\w+)', '@' => '(.+)' }[type]
            end
          }

          if c = /^#{pt}$/i.match(st)
            wantmatch.each_with_index { |wm, i|
              matches[wm] = c.captures[i]
              return false if matches[wm] =~ /^(push|pop|esp)[afd]*$/i
            }
            true
          end
        }
      end

    end
  end
end
