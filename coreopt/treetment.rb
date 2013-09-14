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
    def deep_go(block, rec = MAX_REC_LITE, flow = Flow.new(self))
      raise 'should be a loop' if rec <= 0
      raise 'invalid arg: nil block' if not block

      puts "* deep go at: #{Expression[block.address]} ; rec: #{rec}; comment: #{(block.list.first.comment || []).join(', ')}" if $VERBOSE

      nextb = find_next_blocks(block.address)

      flow.concat block.list
      flow.block_addresses << block.address

      if (block.to_subfuncret.to_a + block.to_normal.to_a).length == 1 and nextb.first and
      (nextb.first.from_subfuncret.to_a + nextb.first.from_normal.to_a).length <= 1
        deep_go(nextb.first.dup, rec-1, flow)
      end
      flow
    end

    # merge_clean :
    #  - rebuild accurate control flow graph based on deep_go method
    #  - apply optimizations on the recovered flow (ex: merge contiguous chunks of code)
    #  - replace optimized code within control flow graph
    def merge_clean(start_addr)
      puts "\n============\n= start to clean at #{Expression[start_addr]}" if $VERBOSE
      flows = build_flows(start_addr)
      optimize_flows(flows)
    end

    def build_flows(start_addr)
      done = [:default, :unkown]
      todo = [start_addr, :start]
      flows = {}

      while todo_info = todo.pop
        current_addr, from = todo_info
        break if not current_addr = normalize(current_addr)
        if flows.include? current_addr
          flows[current_addr][:from] << from
          next
        end
        next if done.include? current_addr
        begin

          done << current_addr
          unless di_at(current_addr)
            raise MyExc, "address is not covered #{Metasm::Expression[current_addr]}"
          end
          current = di_at(current_addr).block

          puts "\nConstructing flow starting #{Expression[current_addr]}"
          flow = deep_go(current)

          last_block  = get_block(flow.block_addresses.last)
          last_block.each_to { |addr, type| todo << [addr, current_addr] }
          flow.original_last_address = last_block.list.last.address
          from_subfuncret = get_block(flow.block_addresses.first).from_subfuncret

          # Only find next blocks within same function
          #
          # When to_subfuncret is not nil, the block ends with a call and to_normal
          # points to the called function. Since we're not interested in the called
          # function, we just use to_subfuncret in this case to get the next address
          # within the function. This obviously assumes that functions return.
          to_list = last_block.to_subfuncret || last_block.to_normal || []

          puts "  lastaddr: #{flow.original_last_address}"

          flow[1..-2].each {|di| replace_instrs(di.address, di.address, []) }

          flows[current_addr] = {:flow => flow,
                                 :from => [from],
                                 :to => to_list,
                                 :from_subfuncret => (from_subfuncret and
                                                      from_subfuncret.length > 0)}

        rescue MyExc
          puts $! if $VERBOSE
          done << current_addr
        end
      end

      flows.each do |address, flow_info|
        flow = flow_info[:flow]
        flow.from = flow_info[:from]
        flow.to = flow_info[:to]
      end

      flows
    end

    # Run optimization on given flows
    def optimize_flows(flows)
      flows.each do |address, flow_info|
        flow = flow_info[:flow]
        flow_back = flow.dup
        first_block = get_block(flow.block_addresses.first)
        firstaddr = first_block.list.first.address

        puts "\n [+] Cleaning flow starting #{Expression[firstaddr]}"
        flow.clean!(flows)

        if not flow.first
          nop = flow_back.first
          transform_di_to_nop(nop)
          flow << nop
        end

        flow.first.address = firstaddr
        puts "    replace_instrs(#{firstaddr}, #{flow.original_last_address}, <Flow with #{flow.size} instructions>)"
        block = replace_instrs(firstaddr, flow.original_last_address, flow)
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

    def transform_di_to_nop(di)
      di.opcode = di.instruction.cpu.opcode_list.find { |op| op.name == 'nop'}
      di.instruction.opname = di.opcode.name
      di.instruction.args = []
      di.backtrace_binding = nil
    end

    class MyExc < RuntimeError ; end
  end
end