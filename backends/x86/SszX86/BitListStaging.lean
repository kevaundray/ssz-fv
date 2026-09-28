import SszX86.BitListCore

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

/-- Four fixed-width stores, based at the real CALL slot. Keeping this memory
block separate prevents proof reduction through the full register state. -/
def stagedMem (m : DataMem) (p pointer payload ra : BitVec 64) : DataMem :=
  let m := Mem.storeInt m (p + BitVec.ofNat 64 40) 8 payload.toInt
  let m := Mem.storeInt m (p + BitVec.ofNat 64 32) 8 pointer.toInt
  let m := Mem.storeInt m (p + BitVec.ofNat 64 24) 8 1
  Mem.storeInt m (p + BitVec.ofNat 64 0) 8 ra.toInt

theorem list_memory (s : MachineData) (pointer payload ra : BitVec 64) :
    (listState s pointer payload ra).dmem =
      stagedMem s.dmem (s.regs.rsp.toBitVec - 8) pointer payload ra := by
  have a : s.regs.rsp.toBitVec - 8 + 40#64 = s.regs.rsp.toBitVec + 32 := by bv_omega
  have b : s.regs.rsp.toBitVec - 8 + 32#64 = s.regs.rsp.toBitVec + 24 := by bv_omega
  have c : s.regs.rsp.toBitVec - 8 + 24#64 = s.regs.rsp.toBitVec + 16 := by bv_omega
  simp only [listState, optionMem, stagedMem, a, b, c, BitVec.add_zero]

theorem staged_mapped (m : DataMem) (p pointer payload ra q : BitVec 64) (n : Nat)
    (h : Large.Mapped m q n) : Large.Mapped (stagedMem m p pointer payload ra) q n := by
  unfold stagedMem
  exact Large.mapped_store _ _ _ _ _ _
    (Large.mapped_store _ _ _ _ _ _ (Large.mapped_store _ _ _ _ _ _
      (Large.mapped_store _ _ _ _ _ _ h)))

theorem staged_frame (m : DataMem) (p pointer payload ra a : BitVec 64)
    (outside : ∀ i < 48, a ≠ p + BitVec.ofNat 64 i) :
    (stagedMem m p pointer payload ra).get? a = m.get? a := by
  unfold stagedMem
  rw [store_frame _ p a 48 0 8 _ (by decide) outside]
  rw [store_frame _ p a 48 24 8 _ (by decide) outside]
  rw [store_frame _ p a 48 32 8 _ (by decide) outside]
  rw [store_frame _ p a 48 40 8 _ (by decide) outside]

theorem stage_read_apart (m : DataMem) (p : BitVec 64) (a n b : Nat) (v : Int)
    (ha : a + n ≤ 48) (hb : b + 8 ≤ 48) (apart : a + n ≤ b ∨ b + 8 ≤ a) :
    Mem.loadInt (Mem.storeInt m (p + BitVec.ofNat 64 b) 8 v)
      (p + BitVec.ofNat 64 a) n = Mem.loadInt m (p + BitVec.ofNat 64 a) n := by
  apply load_store_disjoint
  intro i hi j hj
  bv_omega

theorem store_one_low32 (m : DataMem) (p : BitVec 64) :
    Mem.loadInt (Mem.storeInt m p 8 1) p 4 = some 1 := by
  have observed := memmove_loadInt_of_lookup (Mem.storeInt m p 8 1) p
    (Int.toBytes 4 1) (by
      intro i hi
      have hi4 : i < 4 := by simpa only [Int.toBytes_length] using hi
      unfold Mem.storeInt
      rw [memmove_store_lookup_inside m p (Int.toBytes 8 1) i
        (by simpa only [Int.toBytes_length] using (show i < 8 by omega))
        (by simp only [Int.toBytes_length]; decide)]
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases choices with rfl | rfl | rfl | rfl <;> decide)
  simpa only [Int.toBytes_length, ofBytes_toBytes,
    show (1 : Int).take (8 * 4) = 1 by decide] using observed

theorem stage_signed (v : BitVec 64) : v.toInt.take 64 = (v.toNat : Int) := by
  change v.toInt % 2^64 = (v.toNat : Int)
  rw [BitVec.toInt_eq_toNat_cond]
  have := v.isLt
  split <;> omega

theorem staged_fields (m : DataMem) (p pointer payload ra : BitVec 64) :
    Mem.loadInt (stagedMem m p pointer payload ra) p 8 = some (ra.toNat : Int) ∧
    Mem.loadInt (stagedMem m p pointer payload ra) (p + 24#64) 4 = some 1 ∧
    Mem.loadInt (stagedMem m p pointer payload ra) (p + 32#64) 8 = some (pointer.toNat : Int) ∧
    Mem.loadInt (stagedMem m p pointer payload ra) (p + 40#64) 8 = some (payload.toNat : Int) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [stagedMem, BitVec.add_zero,
      load_store_same _ _ 8 _ (by decide), Nat.reduceMul, stage_signed]
  · unfold stagedMem
    rw [stage_read_apart _ p 24 4 0 _ (by decide) (by decide) (by decide)]
    exact store_one_low32 _ _
  · unfold stagedMem
    rw [stage_read_apart _ p 32 8 0 _ (by decide) (by decide) (by decide)]
    rw [stage_read_apart _ p 32 8 24 _ (by decide) (by decide) (by decide)]
    simp only [load_store_same _ _ 8 _ (by decide), Nat.reduceMul, stage_signed]
  · unfold stagedMem
    rw [stage_read_apart _ p 40 8 0 _ (by decide) (by decide) (by decide)]
    rw [stage_read_apart _ p 40 8 24 _ (by decide) (by decide) (by decide)]
    rw [stage_read_apart _ p 40 8 32 _ (by decide) (by decide) (by decide)]
    simp only [load_store_same _ _ 8 _ (by decide), Nat.reduceMul, stage_signed]

end SszX86.BitList
