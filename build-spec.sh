# disable LH
stack build --fast --ghc-options "-fplugin=LiquidHaskell -fplugin-opt=LiquidHaskell:--compile-spec"