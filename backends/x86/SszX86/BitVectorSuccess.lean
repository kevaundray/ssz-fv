import SszX86.BitVectorPadding

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Success stores the original borrowed slice pointer, including empty input. -/
def successMem (m : DataMem) (out pointer size low high : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 1 3
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 pointer.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 size.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 low.toInt
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 high.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 0

def successReady (s : MachineData) (pointer : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsi := UInt64.ofBitVec pointer}
    dmem := successMem s.dmem s.regs.rdx.toBitVec pointer s.regs.r14.toBitVec
      s.regs.rax.toBitVec s.regs.rcx.toBitVec}

/-- Actual successful construction stores followed by the common native jump. -/
theorem success_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (pointer : BitVec 64)
    (hm : Large.Mapped s.dmem s.regs.rdx.toBitVec 80)
    (hl : Mem.loadInt (Mem.storeInt s.dmem (s.regs.rdx.toBitVec + 16#64) 1 3)
      (s.regs.rsp.toBitVec + 104#64) 8 = some (pointer.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (successReady s pointer, base + 7720)) :
    Eventually (step e) P (s, base + 5317) := by
  bitvector_output 189 at 16 width 1 using hc mapped hm
  bitvector_step 190 using hc
  bitvector_load hl
  bitvector_output 191 at 32 width 8 using hc mapped hm
  bitvector_output 192 at 40 width 8 using hc mapped hm
  bitvector_output 193 at 48 width 8 using hc mapped hm
  bitvector_output 194 at 56 width 8 using hc mapped hm
  bitvector_output 195 at 0 width 8 using hc mapped hm
  bitvector_step 196 using hc
  simpa [successReady, successMem] using next

theorem success_frame (m : DataMem) (out pointer size low high a : BitVec 64)
    (outside : ∀ i < 80, a ≠ out + BitVec.ofNat 64 i) :
    (successMem m out pointer size low high).get? a = m.get? a := by
  simp (disch := first | omega | assumption | decide) only
    [successMem, store_frame (limit := 80)]

private theorem observe_disjoint (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 80 ≤ 2^64) (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 80) (hb : b + k ≤ 80) (apart : a + n ≤ b ∨ b + k ≤ a) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n = observe m out a n := by
  unfold observe
  rw [load_store_offset_disjoint m out bound a n b k value ha hb apart]

private theorem observe_same (m : DataMem) (out : BitVec 64) (off count : Nat) (value : Int)
    (bound : count ≤ 2^64) :
    observe (Mem.storeInt m (out + BitVec.ofNat 64 off) count value) out off count =
      some (value.take (8 * count)).toNat := by
  rw [observe, load_store_same _ _ _ _ bound]
  rfl

private theorem width_observe (m : DataMem) (out : BitVec 64) (off count : Nat) :
    widthLoad m (out.toNat + off) count = observe m out off count := by
  simp only [widthLoad, observe, width_address]

private theorem width_observe_zero (m : DataMem) (out : BitVec 64) (count : Nat) :
    widthLoad m out.toNat count = observe m out 0 count := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

/-- The six initialized fields and borrowed bytes are exactly the shared native
success observation; no requirement is placed on the ignored result padding. -/
theorem success_observed (m : DataMem) (out pointer size low high : BitVec 64)
    (data : Ssz.Bytes) (count : BitVec 128) (bound : out.toNat + 80 ≤ 2^64)
    (sourceBound : pointer.toNat + data.size ≤ 2^64)
    (sourceApart : Body.Apart pointer.toNat data.size out.toNat 80)
    (source : SszNative.ByteView.BytesAt (widthLoad m) pointer.toNat data)
    (sizeValue : size.toNat = data.size)
    (lowValue : low.toNat = count.toNat % 2^64)
    (highValue : high.toNat = count.toNat / 2^64)
    (scope : data.size = (count.toNat + 7) / 8) :
    SszNative.BitVector.ResultAt (widthLoad (successMem m out pointer size low high))
      out.toNat pointer.toNat data (.ok count) := by
  have frame : NatToU128.ByteFrame m (successMem m out pointer size low high) out.toNat 80 := by
    intro a outside
    exact success_frame m out pointer size low high a
      (fun i hi => Body.outside_byte out a 80 i bound outside hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, scope⟩
  · simp (disch := first | assumption | omega | decide) only
      [width_observe_zero, successMem, observe_same, Nat.reduceMul]
    decide
  · simp (disch := first | assumption | omega | decide) only
      [width_observe, successMem, observe_disjoint, observe_same, Nat.reduceMul]
    decide
  · simp (disch := first | assumption | omega | decide) only
      [width_observe, successMem, observe_disjoint, observe_store64]
  · simpa (disch := first | assumption | omega | decide) only
      [width_observe, successMem, observe_disjoint, observe_store64] using congrArg some sizeValue
  · simpa (disch := first | assumption | omega | decide) only
      [width_observe, successMem, observe_disjoint, observe_store64] using congrArg some lowValue
  · simpa (disch := first | assumption | omega | decide) only
      [width_observe, successMem, observe_disjoint, observe_store64] using congrArg some highValue
  · intro i hi
    rw [NatToU128.narrow_width_preserved m _ out.toNat 80 (pointer.toNat + i) 1 frame
      (by omega) (by unfold Body.Apart at *; omega)]
    exact source i hi

end SszX86.BitVector
