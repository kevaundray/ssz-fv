import SszArm.BoolBlocks
import SszArm.BoolJumps
import SszArm.BoolStores
import SszArm.BoolReturn

namespace SszArm.BoolCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def afterJump (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (target : Nat) : ArmState :=
  w .PC (base + BitVec.ofNat 64 target) (storeBlock ops s)

theorem afterJump_code (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (target : Nat)
    (hc : CodeAt s base) : CodeAt (afterJump ops s base target) base := by
  simpa [CodeAt, afterJump, state_simp_rules, storeBlock_program] using hc

theorem afterJump_error (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (target : Nat) :
    read_err (afterJump ops s base target) = read_err s := by
  simpa (config := {decide := true}) only [afterJump, read_err, state_simp_rules]
    using storeBlock_error ops s

theorem afterJump_aligned (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (target : Nat)
    (ha : CheckSPAlignment s) : CheckSPAlignment (afterJump ops s base target) := by
  simpa [afterJump, state_simp_rules] using storeBlock_aligned ops s ha

theorem block_jump (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (start target : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 start)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hwords : ∀ i : Fin ops.length, (start + 4 * i.val, (ops[i]).word) ∈ program)
    (hj : (start + 4 * ops.length, target) ∈ storeJumps) :
    run (ops.length + 1) s = afterJump ops s base target := by
  rw [run_plus, storeBlock_run ops s base start hc hp he ha hwords]
  change stepi (storeBlock ops s) = _
  apply jump_to _ base _ target hj
  · simpa only [CodeAt, storeBlock_program] using hc
  · simp [storeBlock_pc, hp, BitVec.ofNat_add, BitVec.add_assoc]
  · simpa only [storeBlock_error] using he

theorem scope_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 2084#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 49 s = returned (afterJump scopeStores s base 4732) := by
  rw [show 49 = 41 + 8 by decide, run_plus]
  rw [show run 41 s = afterJump scopeStores s base 4732 from
    block_jump scopeStores s base 2084 4732 hc hp he ha (by decide) (by decide)]
  apply epilogue _ base (afterJump_code _ _ _ _ hc)
  · simp [afterJump, state_simp_rules]
  · simpa only [afterJump_error] using he
  · exact afterJump_aligned _ _ _ _ ha

theorem tag_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4504#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 18 s = returned (afterJump tagStores s base 4732) := by
  rw [show 18 = 10 + 8 by decide, run_plus]
  rw [show run 10 s = afterJump tagStores s base 4732 from
    block_jump tagStores s base 4504 4732 hc hp he ha (by decide) (by decide)]
  apply epilogue _ base (afterJump_code _ _ _ _ hc)
  · simp [afterJump, state_simp_rules]
  · simpa only [afterJump_error] using he
  · exact afterJump_aligned _ _ _ _ ha

def successTail (ops : List StoreOp) (s : ArmState) (base : BitVec 64) : ArmState :=
  returned (afterJump tagStores (afterJump ops s base 4504) base 4732)

theorem true_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 628#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 33 s = successTail trueStores s base := by
  rw [show 33 = 15 + 18 by decide, run_plus]
  rw [show run 15 s = afterJump trueStores s base 4504 from
    block_jump trueStores s base 628 4504 hc hp he ha (by decide) (by decide)]
  apply tag_tail _ base (afterJump_code _ _ _ _ hc)
  · simp [afterJump, state_simp_rules]
  · simpa only [afterJump_error] using he
  · exact afterJump_aligned _ _ _ _ ha

theorem false_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4084#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 33 s = successTail falseStores s base := by
  rw [show 33 = 15 + 18 by decide, run_plus]
  rw [show run 15 s = afterJump falseStores s base 4504 from
    block_jump falseStores s base 4084 4504 hc hp he ha (by decide) (by decide)]
  apply tag_tail _ base (afterJump_code _ _ _ _ hc)
  · simp [afterJump, state_simp_rules]
  · simpa only [afterJump_error] using he
  · exact afterJump_aligned _ _ _ _ ha

def badTail (s : ArmState) (base : BitVec 64) : ArmState :=
  returned (tagsStored (reasonStored (tagInitialized (afterJump badStores s base 4720))))

theorem bad_tail (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 4144#64) (he : read_err s = .None) (ha : CheckSPAlignment s) :
    run 50 s = badTail s base := by
  rw [show 50 = 39 + (3 + 8) by decide, run_plus]
  rw [show run 39 s = afterJump badStores s base 4720 from
    block_jump badStores s base 4144 4720 hc hp he ha (by decide) (by decide)]
  rw [run_plus, error_tail _ base (afterJump_code _ _ _ _ hc)
    (by simp [afterJump, state_simp_rules]) (by simpa only [afterJump_error] using he)]
  apply epilogue _ base
  · simpa [CodeAt, tagsStored, reasonStored, tagInitialized, state_simp_rules]
      using afterJump_code badStores s base 4720 hc
  · simp [tagsStored, reasonStored, tagInitialized, afterJump, state_simp_rules, BitVec.add_assoc]
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules]
      using (afterJump_error badStores s base 4720).trans he
  · simpa [tagsStored, reasonStored, tagInitialized, state_simp_rules]
      using afterJump_aligned badStores s base 4720 ha

theorem afterJump_sp (ops : List StoreOp) (s : ArmState) (base : BitVec 64) (target : Nat)
    (h : ops ∈ [trueStores, falseStores, scopeStores, badStores, tagStores]) :
    r (.GPR 31#5) (afterJump ops s base target) = r (.GPR 31#5) s := by
  simpa (config := {decide := true}) [afterJump, state_simp_rules] using stores_sp s ops h

theorem successTail_sp (ops : List StoreOp) (s : ArmState) (base : BitVec 64)
    (h : ops ∈ [trueStores, falseStores, scopeStores, badStores, tagStores]) :
    r (.GPR 31#5) (successTail ops s base) = r (.GPR 31#5) s + 368#64 := by
  rw [successTail, returned_sp, afterJump_sp _ _ _ _ (by decide), afterJump_sp _ _ _ _ h]

theorem successTail_pc (ops : List StoreOp) (s : ArmState) (base : BitVec 64)
    (h : ops ∈ [trueStores, falseStores, scopeStores, badStores, tagStores]) :
    read_pc (successTail ops s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) (successTail ops s base) := by
  unfold successTail
  rw [returned_pc_read, afterJump_sp _ _ _ _ (by decide), afterJump_sp _ _ _ _ h]

theorem badTail_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (badTail s base) = r (.GPR 31#5) s + 368#64 := by
  rw [badTail, returned_sp]
  simp (config := {decide := true}) only [tagsStored, reasonStored, tagInitialized, state_simp_rules]
  rw [afterJump_sp _ _ _ _ (by decide)]

theorem badTail_pc (s : ArmState) (base : BitVec 64) :
    read_pc (badTail s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + 280#64) (badTail s base) := by
  unfold badTail
  rw [returned_pc_read]
  simp (config := {decide := true}) only [tagsStored, reasonStored, tagInitialized, state_simp_rules]
  rw [afterJump_sp _ _ _ _ (by decide)]

theorem successTail_register (ops : List StoreOp) (s : ArmState) (base : BitVec 64)
    (h : ops ∈ [trueStores, falseStores, scopeStores, badStores, tagStores])
    (reg : BitVec 5) (offset : Nat) (hr : (reg, offset) ∈ savedRegisters) :
    r (.GPR reg) (successTail ops s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) (successTail ops s base) := by
  unfold successTail
  rw [returned_register _ reg offset hr, afterJump_sp _ _ _ _ (by decide),
    afterJump_sp _ _ _ _ h]

theorem badTail_register (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (offset : Nat) (hr : (reg, offset) ∈ savedRegisters) :
    r (.GPR reg) (badTail s base) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) (badTail s base) := by
  unfold badTail
  rw [returned_register _ reg offset hr]
  simp (config := {decide := true}) only [tagsStored, reasonStored, tagInitialized, state_simp_rules]
  rw [afterJump_sp _ _ _ _ (by decide)]

end SszArm.BoolCodec
