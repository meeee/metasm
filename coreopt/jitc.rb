class Jitc

  # Jitc class: on-the-fly  binary manipulation
  # typical use case:
  #  - dump optimized code from disassembler
  #  - break down virtualized code
  #  - re-generate code and map it within original target virtual space

  ASM_TMP = 'tmp.asm'
  BIN_TMP = 'tmp.bin'

  # dump function assembly to file
  def func2asm(d, ep, output = ASM_TMP)
    dump_asm(output, d, [ep])
  end

  # dump assembly from shellcode disassembler to binary
  # return Shellcode object
  def sc2bin(sc, addr, ep = 0)
    dump_asm(sc.disassembler, [ep])
    src = File.read(ASM_TMP)
    File.unlink ASM_TMP
    sc_new = Shellcode.new(Ia32.new, addr)
    sc_new.parse src
    sc_new.assemble
    return sc_new
  end

  # return assembly binary data (edata)
  # return edata
  def sc2edata(sc, addr, ep = 0, output = BIN_TMP)
    sc_new = sc2bin(sc, addr, ep)
    data = EncodedData.new(sc_new.encode_string)
    File.open(BIN_TMP, 'wb'){|fd| fd.write data.data} if output
    data
  end

  private

  # walks the program from a serie of entrypoints, returns a list of block -> block in a function and function -> function (2 hashes)
  def dump_makegraph(dasm, eplist)
    # funcaddr => [list of subfuncaddr]
    func_rel = {}
    # blockaddr => [list of blockaddr] (same func only)
    blk_rel = {}

    # build graph
    todo_f = eplist.dup
    done_f = []
    while f = todo_f.shift
      f = dasm.normalize f
      next if done_f.include? f
      done_f << f
      func_rel[f] = []

      todo_b = [f]
      done_b = []
      while b = todo_b.shift
        next if done_b.include? b
        done_b << b
        blk_rel[b] = []
        next if not di = dasm.decoded[b] or di == true
        #			next if not di == true
        di.block.each_to_indirect { |t|
          t = dasm.normalize t
          todo_f << t
          func_rel[f] << t
        }
        if di.block.to_subfuncret
          di.block.each_to_normal { |t|
            t = dasm.normalize t
            todo_f << t
            func_rel[f] << t
          }
          di.block.each_to_subfuncret { |t|
            t = dasm.normalize t
            todo_b << t
            blk_rel[b] << t
          }
        else
          di.block.each_to_normal { |t|
            t = dasm.normalize t
            todo_b << t
            blk_rel[b] << t
          }
        end
        blk_rel[b].uniq!
      end
      func_rel[f].uniq!
    end
    [func_rel, blk_rel]
  end

  # Dump bloc of code to file.
  def dump_asm(filename, dasm, eplist)
    func_rel, blk_rel = dump_makegraph(dasm, eplist)
    maylabel = lambda { |l| dasm.prog_binding.index(l) || l }

    # output file
    File.open(filename, 'w') { |fd|
      todo_f = eplist.dup
      done_f = []
      done_b = []
      while f = todo_f.shift
        next if done_f.include? f
        done_f << f

        if blk_rel[f]
          todo_b = [f]
          while b = todo_b.pop
            next if done_b.include? b or not dasm.decoded[b]
            done_b << b

            block = dasm.decoded[b].block
            dasm.auto_label_at(block.address)
            dasm.dump_block_header(block) { |l| fd.puts l }

            if block.list.last and block.list.last.instruction.opname == 'ret'
              fd.puts "jmp 1f\n1:\n"
            end

            block.list.each { |di|
              l = dasm.prog_binding.index(di.address) if di.address != block.address
              fd.puts "#{l}:" if l
              fd.puts di.show if di.instruction.opname != 'nop'

              if di.opcode.name == 'call' and di.comment.to_a.include? 'noreturn'
                retaddr = di.address + di.bin_length
                if dasm.decoded[retaddr]
                  fd.puts "    jmp #{maylabel[retaddr]}    ; blabla ret"
                else
                  fd.puts "    hlt    ; blabla XXX"
                end
                fd.puts
                fd.puts "#{di.instruction.args.first}:" if di != block.list.last
              end
            }

            to = blk_rel[b].to_a
            todo_b.concat to
            op = block.list.last.opcode if block.list.last
            if to.length == 2 and not op.props[:stopexec] and op.name[0] == ?j and not block.list.empty?
              following = block.list.last.address + block.list.last.bin_length
              todo_b << following
              to = [following]
            end
            case to.length
            when 0
              fd.puts
            when 1
              if done_b.include? to.first
                fd.puts "    jmp #{maylabel[to.first]}	; blabla"
                fd.puts
              end
            else
              fd.puts "; blabla XXX to: #{to.map { |t| Expression[t] }.join(', ')}"
              fd.puts
            end
          end
        end

        func_rel[f].to_a.each { |tf| todo_f << tf }
      end
      fd.puts
    }
  end

end