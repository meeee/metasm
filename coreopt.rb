require 'coreopt/treetment'
require 'coreopt/flow'
require 'coreopt/optimization'

include Metasm
Disassembler.send(:include, CoreOpt)
