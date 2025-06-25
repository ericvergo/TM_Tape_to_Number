import TMTapeToNumber

def main : IO Unit := do
  IO.println "Turing Machine Tape-to-Number Encoding"
  IO.println "======================================="
  IO.println ""
  IO.println "This project formalizes the encoding of Turing machine"
  IO.println "tape contents as integers, with leftward-unbounded tapes."
  IO.println ""
  IO.println "Key components:"
  IO.println "• LeftTape: Finitely-supported function ℤ →₀ Bool"
  IO.println "• LeftTMConfig: TM configuration with leftward-unbounded tape"
  IO.println "• powersSequence: Example generating powers of 2"
  IO.println ""
  IO.println "See TMTapeToNumber.Basic for the full implementation."
