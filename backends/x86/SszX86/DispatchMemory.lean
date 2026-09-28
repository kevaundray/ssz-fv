import SszX86.DispatchPush
import SszX86.UintBodyMemory

namespace SszX86.Dispatch
open BoolCodec UintCodec

def saved (s : MachineData) (ra : BitVec 64) : Saved :=
  ⟨s.regs.rbx.toBitVec, s.regs.r12.toBitVec, s.regs.r13.toBitVec,
    s.regs.r14.toBitVec, s.regs.r15.toBitVec, s.regs.rbp.toBitVec, ra⟩

macro "dispatch_stack_literals" : tactic => `(tactic|
  simp only [show (8 : BitVec 64) = 8#64 by decide,
    show (16 : BitVec 64) = 16#64 by decide,
    show (24 : BitVec 64) = 24#64 by decide,
    show (32 : BitVec 64) = 32#64 by decide,
    show (40 : BitVec 64) = 40#64 by decide,
    show (48 : BitVec 64) = 48#64 by decide])

theorem saved_mapped (s : MachineData) (p : BitVec 64) (n : Nat)
    (hm : Large.Mapped s.dmem p n) : Large.Mapped (savedMem s) p n := by
  unfold savedMem
  repeat' first | exact hm | apply Large.mapped_store

/-- No byte outside the six PUSH destinations changes in the dispatcher. -/
theorem saved_lookup (s : MachineData) (a : BitVec 64)
    (outside : ∀ i < 48, a ≠ s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 i) :
    (savedMem s).get? a = s.dmem.get? a := by
  have unchanged (m : DataMem) (off : Nat) (ho : 8 ≤ off ∧ off ≤ 48) (value : Int) :
      (Mem.storeInt m (s.regs.rsp.toBitVec - BitVec.ofNat 64 off) 8 value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro j hj
    have hj8 : j < 8 := by simpa only [Int.toBytes_length] using hj
    have eq : s.regs.rsp.toBitVec - BitVec.ofNat 64 off + BitVec.ofNat 64 j =
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 (48 - off + j) := by bv_omega
    rw [eq]
    exact outside _ (by omega)
  simp only [savedMem]
  dispatch_stack_literals
  rw [unchanged _ 48 (by decide), unchanged _ 40 (by decide),
    unchanged _ 32 (by decide), unchanged _ 24 (by decide),
    unchanged _ 16 (by decide), unchanged _ 8 (by decide)]

theorem saved_load (s : MachineData) (p : BitVec 64) (n : Nat)
    (outside : ∀ i < n, ∀ j < 48,
      p + BitVec.ofNat 64 i ≠ s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j) :
    Mem.loadInt (savedMem s) p n = Mem.loadInt s.dmem p n := by
  apply memmove_loadInt_congr
  intro i hi
  exact saved_lookup s _ (outside i hi)

theorem saved_region (s : MachineData) (low : 48 ≤ s.regs.rsp.toNat)
    (p n : Nat) (bound : p + n ≤ 2^64)
    (apart : Body.Apart p n (s.regs.rsp.toNat - 48) 48) :
    Mem.loadInt (savedMem s) (BitVec.ofNat 64 p) n =
      Mem.loadInt s.dmem (BitVec.ofNat 64 p) n := by
  apply saved_load
  intro i hi j hj
  simp only [← UInt64.toNat_toBitVec] at low apart
  unfold Body.Apart at apart
  bv_omega

private theorem stack_apart (m : DataMem) (sp : BitVec 64) (a b : Nat)
    (ha : a ≤ 48) (hb : b ≤ 48) (apart : a + 8 ≤ b ∨ b + 8 ≤ a) (v : Int) :
    Mem.loadInt (Mem.storeInt m (sp - BitVec.ofNat 64 b) 8 v)
      (sp - BitVec.ofNat 64 a) 8 = Mem.loadInt m (sp - BitVec.ofNat 64 a) 8 := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

private theorem stored_word (m : DataMem) (p value : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 value.toInt) p 8 =
      some (Int.ofBytes (wordBytes value)) := by
  rw [wordBytes, ← registerBytes_eq_uintBytes, ofBytes_toBytes]
  exact load_store_same m p 8 value.toInt (by decide)

/-- SavedAt is a conclusion of actual stack stores, not an entry assumption. -/
theorem saved_at (s : MachineData) (ra : BitVec 64)
    (ret : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (Int.ofBytes (wordBytes ra))) :
    SavedAt (savedMem s) (s.regs.rsp.toBitVec - 360) (saved s ra) := by
  have offsets (off : BitVec 64) :
      s.regs.rsp.toBitVec - 360 + off = s.regs.rsp.toBitVec - (360 - off) := by bv_omega
  simp only [SavedAt, saved, offsets, BitVec.reduceSub]
  constructor
  · exact stored_word _ _ _
  constructor
  · unfold savedMem
    dispatch_stack_literals
    rw [stack_apart _ s.regs.rsp.toBitVec 40 48 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  constructor
  · unfold savedMem
    dispatch_stack_literals
    rw [stack_apart _ s.regs.rsp.toBitVec 32 48 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 32 40 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  constructor
  · unfold savedMem
    dispatch_stack_literals
    rw [stack_apart _ s.regs.rsp.toBitVec 24 48 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 24 40 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 24 32 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  constructor
  · unfold savedMem
    dispatch_stack_literals
    rw [stack_apart _ s.regs.rsp.toBitVec 16 48 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 16 40 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 16 32 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 16 24 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  constructor
  · unfold savedMem
    dispatch_stack_literals
    rw [stack_apart _ s.regs.rsp.toBitVec 8 48 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 40 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 32 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 24 (by decide) (by decide) (by decide),
      stack_apart _ s.regs.rsp.toBitVec 8 16 (by decide) (by decide) (by decide)]
    exact stored_word _ _ _
  · simpa only [BitVec.sub_zero, ret] using saved_load s s.regs.rsp.toBitVec 8
      (by intro i hi j hj; bv_omega)

theorem saved_table (s : MachineData) (base : Int64) (table : TableAt s.dmem base)
    (apart : ∀ i < tableBytes.length, ∀ j < 48,
      tableAddress base + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j) :
    TableAt (savedMem s) base := by
  intro i hi
  rw [saved_lookup s _ (apart i hi)]
  exact table i hi

end SszX86.Dispatch
