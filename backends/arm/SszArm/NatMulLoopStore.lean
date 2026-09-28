import SszArm.NatMulExec
import SszArm.NatAddLoopMemory

namespace SszArm.NatMul

inductive LoopStoreSite where
  | output | carry
  deriving DecidableEq

def LoopStoreSite.start : LoopStoreSite → Nat
  | .output => 888 | .carry => 976

def LoopStoreSite.pointer : LoopStoreSite → BitVec 5
  | .output => 11#5 | .carry => 20#5

def LoopStoreSite.index : LoopStoreSite → BitVec 5
  | .output => 16#5 | .carry => 0#5

def LoopStoreSite.source : LoopStoreSite → BitVec 5
  | .output => 18#5 | .carry => 15#5

def LoopStoreSite.ops : LoopStoreSite → List Op
  | .output => [.p888, .p892, .p896, .p900, .p904, .p908, .p912, .p916]
  | .carry => [.p976, .p980, .p984, .p988, .p992, .p996, .p1000, .p1004]

def LoopStoreSite.address (site : LoopStoreSite) (s : ArmState) : BitVec 64 :=
  r (.GPR site.pointer) s + (r (.GPR site.index) s <<< 3)

def loopStoreMemory (site : LoopStoreSite) (s : ArmState) : ArmState :=
  write_mem_bytes 8 (site.address s) (r (.GPR site.source) s) (NatCompare.saved s 9#5)

def loopStored (site : LoopStoreSite) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (site.start + 32)) (loopStoreMemory site s)

theorem loop_store_restore (site : LoopStoreSite) (s : ArmState)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64)
    (separate : (site.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (site.address s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (loopStoreMemory site s) =
      r (.GPR 9#5) s := by
  unfold loopStoreMemory
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
    (by bv_omega) physical (by bv_omega)]
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)

theorem loop_store_run (site : LoopStoreSite) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64)
    (separate : (site.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (site.address s).toNat) :
    run 8 s = loopStored site s base := by
  have restored := loop_store_restore site s stack physical separate
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := pc
  have follows : Follows base site.ops s := by
    cases site <;> simp [LoopStoreSite.ops, LoopStoreSite.start, Follows, Op.row, Op.effect,
      put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = site.ops.length by cases site <;> rfl,
    block_run base site.ops s code error aligned follows]
  have effect : block base site.ops s = w .PC (read_pc s + 32#64) (loopStoreMemory site s) := by
    cases site with
    | output =>
      change NatAdd.indexedStoreSequence s 11#5 16#5 9#5 18#5 = _
      exact NatAdd.indexedStoreSequence_eq s 11#5 16#5 9#5 18#5
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) restored
    | carry =>
      change NatAdd.indexedStoreSequence s 20#5 0#5 9#5 15#5 = _
      exact NatAdd.indexedStoreSequence_eq s 20#5 0#5 9#5 15#5
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) restored
  rw [effect]
  simp only [loopStored, pc, BitVec.ofNat_add, BitVec.add_assoc]

end SszArm.NatMul
