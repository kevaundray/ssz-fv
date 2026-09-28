import SszX86.SerializeDecode
import SszX86.NatDivisionStack
import SszX86.BitVectorMapping

namespace SszX86.Serialize
open BoolCodec UintCodec

/-- The wrapper saves exactly five registers; RBP is never touched. -/
def savedMem (s : MachineData) : DataMem :=
  let m := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 s.regs.r15.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 16) 8 s.regs.r14.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 24) 8 s.regs.r13.toBitVec.toInt
  let m := Mem.storeInt m (s.regs.rsp.toBitVec - 32) 8 s.regs.r12.toBitVec.toInt
  Mem.storeInt m (s.regs.rsp.toBitVec - 40) 8 s.regs.rbx.toBitVec.toInt

def savedState (s : MachineData) : MachineData :=
  {s with dmem := savedMem s
          regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 40)}}

/-- State immediately before CALL42. The live Plan occupies exactly 72 bytes. -/
def prologueState (s : MachineData) : MachineData :=
  {s with
    dmem := savedMem s
    regs := {s.regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 136)
      r13 := s.regs.r8
      r14 := s.regs.rcx
      r15 := s.regs.rdx
      r12 := s.regs.rsi
      rbx := s.regs.rdi
      rdi := UInt64.ofBitVec (s.regs.rsp.toBitVec - 112)
      rcx := s.regs.r9
      r8 := 1}
    status := Udivti3.subFlags (s.regs.rsp.toBitVec - 40) 96}

/-- The only memory effect of either wrapper CALL is its eight-byte return slot. -/
def callState (s : MachineData) (ra : BitVec 64) : MachineData :=
  {s with
    regs := {s.regs with rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 8)}
    dmem := Mem.storeInt s.dmem (s.regs.rsp.toBitVec - 8) 8 ra.toInt}

def measureMem (s : MachineData) (base : Int64) : DataMem :=
  Mem.storeInt (savedMem s) (s.regs.rsp.toBitVec - 144) 8 (base + 47).toBitVec.toInt

/-- Concrete original-state image at the linked measurement entry. -/
def measureState (s : MachineData) (base : Int64) : MachineData :=
  {prologueState s with
    dmem := measureMem s base
    regs := {(prologueState s).regs with
      rsp := UInt64.ofBitVec (s.regs.rsp.toBitVec - 144)}}

theorem measureState_eq_call (s : MachineData) (base : Int64) :
    measureState s base = callState (prologueState s) (base + 47).toBitVec := by
  simp [measureState, measureMem, callState, prologueState, BitVec.sub_sub]

/-- An arbitrary original mapped stack suffices for every PUSH and the CALL. -/
theorem activation_load (m : DataMem) (sp : BitVec 64) (distance : Nat)
    (hm : Large.Mapped m (sp - 144) 144)
    (lo : 8 ≤ distance) (hi : distance ≤ 144) :
    ∃ old, Mem.loadInt m (sp - BitVec.ofNat 64 distance) 8 = some old := by
  have address : sp - BitVec.ofNat 64 distance =
      (sp - 144) + BitVec.ofNat 64 (144-distance) := by bv_omega
  rw [address]
  exact Large.mapped_load m (sp - 144) 144 (144-distance) 8 hm (by omega)

theorem savedMem_mapped (s : MachineData) (p : BitVec 64) (count : Nat)
    (hm : Large.Mapped s.dmem p count) : Large.Mapped (savedMem s) p count := by
  unfold savedMem
  repeat' apply Large.mapped_store
  exact hm

theorem savedMem_extension (s : MachineData) :
    BitVector.Mapping.Extends s.dmem (savedMem s) :=
  savedMem_mapped s

theorem callState_extension (s : MachineData) (ra : BitVec 64) :
    BitVector.Mapping.Extends s.dmem (callState s ra).dmem :=
  BitVector.Mapping.Extends.store _ _ _ _

theorem measureState_extension (s : MachineData) (base : Int64) :
    BitVector.Mapping.Extends s.dmem (measureState s base).dmem := by
  intro p count hm
  apply Large.mapped_store
  exact savedMem_mapped s p count hm

/-- These are the exact saved-register writes, not the whole reserved frame. -/
theorem savedMem_frame (s : MachineData) :
    Emit.MemoryFrame s.dmem (savedMem s)
      (fun a => Emit.InSpan a (s.regs.rsp.toBitVec - 40) 40) := by
  intro a outside
  have untouched : ∀ i < 40, a ≠ (s.regs.rsp.toBitVec - 40) + BitVec.ofNat 64 i := by
    intro i hi equal
    exact outside ⟨i, hi, equal⟩
  simp (disch := first | assumption | decide | omega) only
    [savedMem, BitVec.ofNat_eq_ofNat, NatDivision.stack_store_frame (span := 40)]

theorem callState_frame (s : MachineData) (ra : BitVec 64) :
    Emit.MemoryFrame s.dmem (callState s ra).dmem
      (fun a => Emit.InSpan a (s.regs.rsp.toBitVec - 8) 8) := by
  intro a outside
  apply memmove_store_lookup_outside
  intro i hi equal
  exact outside ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩

/-- Local scratch and the Plan have not been written on entry to Measure. -/
theorem measureState_frame (s : MachineData) (base : Int64) :
    Emit.MemoryFrame s.dmem (measureState s base).dmem
      (fun a => Emit.InSpan a (s.regs.rsp.toBitVec - 40) 40 ∨
        Emit.InSpan a (s.regs.rsp.toBitVec - 144) 8) := by
  intro a outside
  change (Mem.storeInt (savedMem s) (s.regs.rsp.toBitVec - 144) 8
    (base + 47).toBitVec.toInt).get? a = s.dmem.get? a
  unfold Mem.storeInt
  rw [memmove_store_lookup_outside]
  · exact savedMem_frame s a (fun inside => outside (Or.inl inside))
  · intro i hi equal
    exact outside (Or.inr ⟨i, by simpa only [Int.toBytes_length] using hi, equal⟩)

theorem measureState_load_preserved (s : MachineData) (base : Int64)
    (p : BitVec 64) (count : Nat)
    (savedApart : Large.Disjoint p (s.regs.rsp.toBitVec - 40) count 40)
    (callApart : Large.Disjoint p (s.regs.rsp.toBitVec - 144) count 8) :
    Mem.loadInt (measureState s base).dmem p count = Mem.loadInt s.dmem p count := by
  apply memmove_loadInt_congr
  intro i hi
  apply measureState_frame s base
  intro inside
  rcases inside with ⟨j, hj, equal⟩ | ⟨j, hj, equal⟩
  · exact savedApart i hi j hj equal
  · exact callApart i hi j hj equal

/-- The current wrapper stack pointer is 136 below the original caller pointer. -/
structure SavedAt (m : DataMem) (sp : BitVec 64) (original : MachineData) : Prop where
  rbx : Mem.loadInt m (sp + 96#64) 8 = some (original.regs.rbx.toBitVec.toInt.take 64)
  r12 : Mem.loadInt m (sp + 104#64) 8 = some (original.regs.r12.toBitVec.toInt.take 64)
  r13 : Mem.loadInt m (sp + 112#64) 8 = some (original.regs.r13.toBitVec.toInt.take 64)
  r14 : Mem.loadInt m (sp + 120#64) 8 = some (original.regs.r14.toBitVec.toInt.take 64)
  r15 : Mem.loadInt m (sp + 128#64) 8 = some (original.regs.r15.toBitVec.toInt.take 64)

theorem savedAt_congr (m n : DataMem) (sp : BitVec 64) (original : MachineData)
    (same : ∀ i < 40, n.get? (sp + 96#64 + BitVec.ofNat 64 i) =
      m.get? (sp + 96#64 + BitVec.ofNat 64 i)) (saved : SavedAt m sp original) :
    SavedAt n sp original := by
  have contents (distance : Nat) (lo : 96 ≤ distance) (hi : distance + 8 ≤ 136) :
      Mem.loadInt n (sp + BitVec.ofNat 64 distance) 8 =
        Mem.loadInt m (sp + BitVec.ofNat 64 distance) 8 := by
    apply memmove_loadInt_congr
    intro i inside
    have address : sp + BitVec.ofNat 64 distance + BitVec.ofNat 64 i =
        sp + 96#64 + BitVec.ofNat 64 (distance-96+i) := by bv_omega
    rw [address]
    exact same (distance-96+i) (by omega)
  exact ⟨(contents 96 (by decide) (by decide)).trans saved.rbx,
    (contents 104 (by decide) (by decide)).trans saved.r12,
    (contents 112 (by decide) (by decide)).trans saved.r13,
    (contents 120 (by decide) (by decide)).trans saved.r14,
    (contents 128 (by decide) (by decide)).trans saved.r15⟩

theorem savedMem_saved (s : MachineData) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 136) s := by
  have address (a : Nat) (ha : a ≤ 136) :
      s.regs.rsp.toBitVec - 136 + BitVec.ofNat 64 a =
        s.regs.rsp.toBitVec - BitVec.ofNat 64 (136-a) := by bv_omega
  constructor
  all_goals
    simp (disch := decide) only [address, Nat.reduceSub]
    simp (disch := first | decide | omega) only
      [savedMem, BitVec.ofNat_eq_ofNat, Delimited.stack_load_apart,
        BoolCodec.load_store_same, Nat.reduceMul]

/-- CALL's lower word is disjoint from all five saved-register slots. -/
theorem callState_saved (s original : MachineData) (ra : BitVec 64)
    (saved : SavedAt s.dmem s.regs.rsp.toBitVec original) :
    SavedAt (callState s ra).dmem s.regs.rsp.toBitVec original := by
  apply savedAt_congr s.dmem _ s.regs.rsp.toBitVec original _ saved
  intro i hi
  apply callState_frame
  rintro ⟨j, hj, equal⟩
  bv_omega

theorem measureState_saved (s : MachineData) (base : Int64) :
    SavedAt (measureState s base).dmem (s.regs.rsp.toBitVec - 136) s := by
  rw [measureState_eq_call]
  exact callState_saved (prologueState s) s (base + 47).toBitVec (savedMem_saved s)

theorem callState_return_load (s : MachineData) (ra : BitVec 64) :
    Mem.loadInt (callState s ra).dmem (callState s ra).regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
  simp only [callState, UInt64.toBitVec_ofBitVec]
  rw [BoolCodec.load_store_same _ _ 8 _ (by decide)]
  simp only [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]

theorem measureState_return_load (s : MachineData) (base : Int64) :
    Mem.loadInt (measureState s base).dmem (measureState s base).regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes (base + 47).toBitVec)) := by
  rw [measureState_eq_call]
  exact callState_return_load _ _

/-- The original caller return slot survives both the pushes and CALL42. -/
theorem measureState_caller_return (s : MachineData) (base : Int64) :
    Mem.loadInt (measureState s base).dmem s.regs.rsp.toBitVec 8 =
      Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 := by
  apply measureState_load_preserved
  · intro i hi j hj
    bv_omega
  · intro i hi j hj
    bv_omega

/-- The initialized save slots end exactly where the 72-byte Plan begins below. -/
theorem measureState_plan_preserved (s : MachineData) (base : Int64) :
    Mem.loadInt (measureState s base).dmem (s.regs.rsp.toBitVec - 112) 72 =
      Mem.loadInt s.dmem (s.regs.rsp.toBitVec - 112) 72 := by
  apply measureState_load_preserved
  · intro i hi j hj
    bv_omega
  · intro i hi j hj
    bv_omega

end SszX86.Serialize
