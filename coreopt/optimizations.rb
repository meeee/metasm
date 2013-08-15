module Metasm
  module CoreOpt
    module Optimizations
    end
  end
end

require_relative 'optimizations/constant_propagation'
require_relative 'optimizations/declaration_cleaner'
