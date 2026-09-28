import SszX86.BitVectorReturn

namespace SszX86.BitVector
open SszNative UintCodec BoolCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Store order of the actual nonzero-padding rejection path. -/
def paddingMem (m : DataMem) (out : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 15
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

macro "bitvector_output " row:num " at " off:num " width " byteCount:num
    " using " hc:term " mapped " hm:term : tactic => do
  let loadTac ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := 80) (byteCount := $byteCount))
  else
    `(tactic| apply UintCodec.Large.mapped_load (capacity := 80)
      («offset» := $off) («width» := $byteCount))
  `(tactic|
    (bitvector_step $row using $hc
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $loadTac
       · repeat' first | exact $hm | apply UintCodec.Large.mapped_store
       · decide
     simp only [Effects.All]))

/-- Every rejection store and the real jump into the common epilogue. -/
theorem padding_stores_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : Large.Mapped s.dmem s.regs.rax.toBitVec 80)
    (P : MachineState → Prop)
    (next : Eventually (step e) P
      ({s with dmem := paddingMem s.dmem s.regs.rax.toBitVec}, base + 7720)) :
    Eventually (step e) P (s, base + 4885) := by
  bitvector_output 157 at 64 width 8 using hc mapped hm
  bitvector_output 158 at 56 width 8 using hc mapped hm
  bitvector_output 159 at 48 width 8 using hc mapped hm
  bitvector_output 160 at 40 width 8 using hc mapped hm
  bitvector_output 161 at 32 width 8 using hc mapped hm
  bitvector_output 162 at 24 width 8 using hc mapped hm
  bitvector_output 163 at 8 width 8 using hc mapped hm
  bitvector_output 164 at 16 width 8 using hc mapped hm
  bitvector_output 165 at 72 width 4 using hc mapped hm
  bitvector_output 166 at 0 width 8 using hc mapped hm
  bitvector_step 167 using hc
  simpa [paddingMem] using next

theorem padding_frame (m : DataMem) (out : BitVec 64) (a : BitVec 64)
    (outside : ∀ i < 76, a ≠ out + BitVec.ofNat 64 i) :
    (paddingMem m out).get? a = m.get? a := by
  simp (disch := first | omega | assumption | decide) only
    [paddingMem, store_frame (limit := 76)]

private theorem output_observe (m : DataMem) (out : BitVec 64) (off count : Nat) :
    widthLoad m (out.toNat + off) count = observe m out off count := by
  simp only [widthLoad, observe, width_address]

private theorem output_observe_zero (m : DataMem) (out : BitVec 64) (count : Nat) :
    widthLoad m out.toNat count = observe m out 0 count := by
  simp only [widthLoad, observe, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]

/-- The native PaddingBits error has no fabricated Nat payload. -/
theorem padding_observed (m : DataMem) (out : BitVec 64) (bound : out.toNat + 80 ≤ 2^64) :
    SszNative.UintCodec.errorAt (widthLoad (paddingMem m out)) out.toNat 15 0 0 := by
  refine ⟨?_, ?_, ?_, Or.inl ⟨?_, by decide⟩, Or.inl ⟨?_, by decide⟩,
    Or.inl ⟨?_, by decide⟩, ?_⟩
  all_goals
    simp (disch := first | assumption | omega | decide) only
      [SszNative.NatMemory.smallAt, Nat.add_assoc, Nat.reduceAdd,
        output_observe, output_observe_zero, observe, paddingMem,
        load_store_offset_disjoint, load_store_same, Nat.reduceMul]
    decide

end SszX86.BitVector
