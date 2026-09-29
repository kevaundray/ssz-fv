import SszX86.CodecMeasureFixedArithmeticMapped

namespace SszX86.CodecMeasureFixed

/-- Instruction-fetch premises for the actual linked callees reached by fixed
measurement. These assert code bytes/labels, never future helper behavior. -/
structure Environment (e : Executable) (base : Int64) : Prop where
  code : CodeAt e base
  add : NatAdd.CodeAt e (base + Int64.ofInt (-64672))
  division : NatDivision.CodeAt e (base + Int64.ofInt (-72976))
  divisionLowering : Udivti3.Embedded.CodeAt e
    ((base + Int64.ofInt (-72976)) + Int64.ofNat NatDivision.udivOffset)
  multiply : NatMul.CodeAt e (base + Int64.ofInt (-61792))
  multiplyWord : NatMulWord.CodeAt e ((base + Int64.ofInt (-61792)) + 832)
  memset : MemsetCall.MemsetCodeAt e ((base + Int64.ofInt (-61792)) + 148928)

end SszX86.CodecMeasureFixed
