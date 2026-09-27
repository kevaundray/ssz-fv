import SszX86.DelimitedMath

namespace SszX86.Delimited
open UintCodec

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Store order is the linked early-error order, including the final result tag. -/
def earlyMem (m : DataMem) (out : BitVec 64) (reason : BitVec 32) : DataMem :=
  let m := Mem.storeInt m (out + BitVec.ofNat 64 8) 8 1
  let m := Mem.storeInt m (out + BitVec.ofNat 64 16) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 24) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 32) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 40) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 48) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 56) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 64) 8 0
  let m := Mem.storeInt m (out + BitVec.ofNat 64 72) 4 reason.toInt
  Mem.storeInt m (out + BitVec.ofNat 64 0) 8 1

def earlyReady (s : MachineData) (reason : BitVec 32) : MachineData :=
  {s with
    dmem := earlyMem s.dmem s.regs.rdi.toBitVec reason
    regs := {s.regs with rax := 1}}

theorem early_frame (m : DataMem) (out : BitVec 64) (reason : BitVec 32)
    (a : BitVec 64) (outside : ∀ i < 76, a ≠ out + BitVec.ofNat 64 i) :
    (earlyMem m out reason).get? a = m.get? a := by
  simp (disch := first | assumption | omega | decide) only
    [earlyMem, BoolCodec.store_frame (limit := 76)]

theorem observe_same (m : DataMem) (out : BitVec 64)
    (offset byteCount : Nat) (value : Int) (hb : byteCount ≤ 2^64) :
    BoolCodec.observe (Mem.storeInt m (out + BitVec.ofNat 64 offset) byteCount value)
      out offset byteCount = some (value.take (8 * byteCount)).toNat := by
  rw [BoolCodec.observe, BoolCodec.load_store_same m _ byteCount value hb]
  rfl

theorem observe_apart (m : DataMem) (out : BitVec 64)
    (bound : out.toNat + 76 ≤ 2^64) (a n b k : Nat) (value : Int)
    (ha : a + n ≤ 76) (hb : b + k ≤ 76) (apart : a + n ≤ b ∨ b + k ≤ a) :
    BoolCodec.observe (Mem.storeInt m (out + BitVec.ofNat 64 b) k value) out a n =
      BoolCodec.observe m out a n := by
  unfold BoolCodec.observe
  rw [BoolCodec.load_store_disjoint]
  intro i hi j hj
  bv_omega

theorem early_result (m : DataMem) (out : BitVec 64) (reason : BitVec 32)
    (bound : out.toNat + 76 ≤ 2^64) :
    SszNative.UintCodec.errorAt (widthLoad (earlyMem m out reason)) out.toNat
      reason.toNat 0 0 := by
  have rz : reason.toInt.take 32 = (reason.toNat : Int) := by
    change reason.toInt % 4294967296 = (reason.toNat : Int)
    rw [BitVec.toInt_eq_toNat_cond]
    have hr := reason.isLt
    split <;> omega
  have observes (offset byteCount : Nat) :
      widthLoad (earlyMem m out reason) (out.toNat + offset) byteCount =
        BoolCodec.observe (earlyMem m out reason) out offset byteCount := by
    simp only [widthLoad, BoolCodec.observe, width_address]
  have observeZero (byteCount : Nat) :
      widthLoad (earlyMem m out reason) out.toNat byteCount =
        BoolCodec.observe (earlyMem m out reason) out 0 byteCount := by
    simpa using observes 0 byteCount
  refine ⟨?_, ?_, ?_, Or.inl ⟨⟨?_, ?_⟩, by decide⟩,
    Or.inl ⟨⟨?_, ?_⟩, by decide⟩, Or.inl ⟨⟨?_, ?_⟩, by decide⟩, ?_⟩
  all_goals simp only [Nat.add_assoc, Nat.reduceAdd, observes, observeZero]
  all_goals
    simp (disch := first | assumption | omega | decide) only
      [earlyMem, observe_apart, observe_same, Nat.reduceMul, rz, Int.toNat_natCast]
  all_goals decide

/-- The empty-input path writes its complete error and reaches its actual RET. -/
theorem empty_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (hp : Eventually (step e) P (earlyReady s 16#32, base + 232)) :
    Eventually (step e) P (s, base + 153) := by
  delimited_output 41 at 8 width 8 using hc mapped hm
  delimited_output 42 at 16 width 8 using hc mapped hm
  delimited_output 43 at 24 width 8 using hc mapped hm
  delimited_output 44 at 32 width 8 using hc mapped hm
  delimited_output 45 at 40 width 8 using hc mapped hm
  delimited_output 46 at 48 width 8 using hc mapped hm
  delimited_output 47 at 56 width 8 using hc mapped hm
  delimited_output 48 at 64 width 8 using hc mapped hm
  delimited_output 49 at 72 width 4 using hc mapped hm
  delimited_step 50 using hc
  delimited_output 51 at 0 width 8 using hc mapped hm
  simpa [earlyReady, earlyMem] using hp

/-- All-zero and trailing-zero errors share these stores, without stack writes. -/
theorem zero_stores (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (hm : OutputMapped s) (P : MachineState → Prop)
    (hp : Eventually (step e) P
      (earlyReady s (s.regs.rax.toBitVec.setWidth 32), base + 662)) :
    Eventually (step e) P (s, base + 587) := by
  delimited_output 138 at 8 width 8 using hc mapped hm
  delimited_output 139 at 16 width 8 using hc mapped hm
  delimited_output 140 at 24 width 8 using hc mapped hm
  delimited_output 141 at 32 width 8 using hc mapped hm
  delimited_output 142 at 40 width 8 using hc mapped hm
  delimited_output 143 at 48 width 8 using hc mapped hm
  delimited_output 144 at 56 width 8 using hc mapped hm
  delimited_output 145 at 64 width 8 using hc mapped hm
  delimited_output 146 at 72 width 4 using hc mapped hm
  delimited_step 147 using hc
  delimited_output 148 at 0 width 8 using hc mapped hm
  simpa [earlyReady, earlyMem] using hp

def EntryFrame (s t : MachineData) : Prop :=
  t.dmem = s.dmem ∧ t.zmms = s.zmms ∧
  ∀ r, r ≠ .rax → t.regs.get64 r = s.regs.get64 r

/-- The callee checks emptiness before reading any byte or option/arena field. -/
theorem entry_length (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (hp : ∀ flags, Eventually (step e) P
      ({s with status := flags}, if s.regs.rcx = 0 then base + 153 else base + 9)) :
    Eventually (step e) P (s, base) := by
  have target := hc.targets ("delimited_u153", 153) (by decide)
  rw [← Int64.add_zero base]
  delimited_step 0 using hc
  constructor <;> delimited_step 1 using hc
  all_goals
    by_cases hz : s.regs.rcx = 0
    · simpa [hz, target, StatusFlags.from_result, Effects.All] using hp _
    · have hb : s.regs.rcx.toBitVec ≠ 0#64 := by
        intro h
        apply hz
        exact UInt64.toBitVec_inj.1 h
      simpa [hz, hb, StatusFlags.from_result, Effects.All] using hp _

end SszX86.Delimited
