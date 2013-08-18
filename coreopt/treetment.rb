module Metasm
  module CoreOpt

    # treetment.rb
    # CoreOpt methods dedicated to control graph walkthrough and transformation

    MAX_REC = 20
    MAX_REC_LITE = 200
    MAX_BLOC = 32

    attr_accessor :counter

    private

    def find_next_blocks(addr)
      if di = di_at(addr)
        current = di.block
        next_blocks = []

        if current.to_subfuncret
          current.each_to_subfuncret{|a| (b = block_at(a)) ? next_blocks << b : nil }
        else
          current.each_to_normal{|a| (b = block_at(a)) ? next_blocks << b : nil }
        end

        return next_blocks
      else
        raise MyExc, "address is not covered #{Metasm::Expression[addr]}"
      end
    end

    public

    # check if the given address is within a code section
    # (acrobatic check)
    def is_code_section(addr)
      s = section_info_at(normalize(addr))
      return false if not s
      return false if ['.data', '.radata', '.rsrc'].include? s.first
      true
    end

    # control flow graph deep walktrough
    def deep_go(block, locals =[], rec = MAX_REC_LITE, flow = Flow.new(self))
      raise 'should be a loop' if rec <= 0
      raise 'invalid arg: nil block' if not block

      puts "* deep go at: #{Expression[block.address]} ; rec: #{rec}; comment: #{(block.list.first.comment || []).join(', ')}" if $VERBOSE

      nextb = find_next_blocks(block.address)

      flow.concat block.list
      locals << block.address

      if (block.to_subfuncret.to_a + block.to_normal.to_a).length == 1 and nextb.first and
      (nextb.first.from_subfuncret.to_a + nextb.first.from_normal.to_a).length <= 1
        deep_go(nextb.first.dup, locals, rec-1, flow)
      end
      flow
    end

    # merge_clean :
    #  - rebuild accurate control flow graph based on deep_go method
    #  - apply optimizations on the recovered flow (ex: merge contiguous chunks of code)
    #  - replace optimized code within control flow graph
    def merge_clean(start_addr)
      puts "\n============\n= start to clean at #{Expression[start_addr]}" if $VERBOSE
      done = [:default, :unkown]
      todo = [start_addr]

      while current_addr = normalize(todo.pop)
        puts "\n======\n= pop addr #{Expression[current_addr]}" if $VERBOSE
        next if done.include? current_addr
        begin

          done << current_addr
          unless di_at(current_addr)
            raise MyExc, "address is not covered #{Metasm::Expression[current_addr]}"
          end
          current = di_at(current_addr).block

          puts "Constructing flow starting #{current_addr}"
          flow = deep_go(current, locals = [])

          firstb = get_block(locals.first)
          lastb  = get_block(locals.last)
          lastb.each_to { |addr, type| todo << addr }
          firstaddr = firstb.list.first.address
          lastaddr = lastb.list.last.address

          flow[1..-2].each {|di| replace_instrs(di.address, di.address, []) }

          flow_back = flow.dup
          flow.clean!

          if not flow.first
            nop = flow_back.first
            nop.opcode = nop.instruction.cpu.opcode_list.find { |op| op.name == 'nop'}
            nop.instruction.opname = nop.opcode.name
            nop.instruction.args = []
            nop.backtrace_binding = nil
            flow << nop
          end

          flow.first.address = firstaddr
          block = replace_instrs(firstaddr, lastaddr, flow)
        rescue MyExc
          puts $! if $VERBOSE
          done << current_addr
        end
      end
    end

    # return section information for a given address
    def section_info_at(addr)
      addr = normalize(addr)
      return nil if not addr or not addr.kind_of? Integer
      return section_info.find { |n, a, l, i| addr >= a and addr < a+l }
    end

    # make sure code at a given address is disassembled
    def eval_addr(addr)
      addr = normalize(addr)
      disassemble_fast([addr])
      addr
    end

    # get_block: return the block which contained the given address
    def get_block(addr)
      return di_at(eval_addr(addr)).block
    end

    class MyExc < RuntimeError ; end
  end
end