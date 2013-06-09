require 'coreopt/treetment'
require 'coreopt/flow'
require 'coreopt/optimization'

Metasm::Disassembler.send(:include, Metasm::CoreOpt)
