import SszX86.MeasureBool
import SszX86.MeasureUintBody
import SszX86.MeasureBytesBody
import SszX86.MeasureBitsBody
import SszX86.MeasureEntryOwned

namespace SszX86.Measure
open SszNative SszNative.Serialize

/-- All primitive bodies start only after the genuine dispatcher. Original
ownership supplies their inputs and scratch; no semantic success is assumed. -/
theorem bodies_run (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helpers : HelpersAt e base) (s body : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (anchors : AtBody s body)
    (tag : body.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value)) :
    Eventually (step e)
      (fun final => final.2 = base + 3335 ∧
        BodyPost body desc value buffer address capacity used final.1)
      (body, base + Int64.ofNat (bodyEntry desc)) := by
  have bodyOwned := owned.at_body anchors tag
  cases desc with
  | bool =>
    exact bool_body_runs e base hc body value buffer address capacity used bodyOwned
  | uint logicalWidth =>
    exact uint_body_correct e base hc body logicalWidth value buffer address capacity used bodyOwned
  | byteVector length =>
    exact Bytes.vector_body e base hc body length value buffer address capacity used bodyOwned
  | byteList limit =>
    exact Bytes.list_body e base hc body limit value buffer address capacity used bodyOwned
  | bitVector length =>
    exact bitvector_body_correct e base hc body length value buffer address capacity used bodyOwned
  | bitList limit =>
    exact bitlist_body_correct e base hc helpers body limit value buffer address capacity used bodyOwned
  | progressiveBitList limit =>
    exact progressive_body_correct e base hc helpers body limit value buffer address capacity used bodyOwned

end SszX86.Measure
