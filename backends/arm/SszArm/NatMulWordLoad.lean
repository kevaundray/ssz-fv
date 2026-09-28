import SszArm.NatMulWordExec
import SszArm.NatCompareBlocks
import SszArm.NatAddLoadState

namespace SszArm.NatMulWord

inductive LoadSite where
  | identity | trim | input
  deriving DecidableEq

def LoadSite.start : LoadSite → Nat
  | .identity => 116 | .trim => 260 | .input => 600

def LoadSite.scratch : LoadSite → BitVec 5
  | .identity => 11#5 | .trim => 12#5 | .input => 9#5

def LoadSite.destination : LoadSite → BitVec 5
  | .identity => 10#5 | .trim => 11#5 | .input => 17#5

def LoadSite.ops : LoadSite → List Op
  | .identity => [.p116, .p120, .p124, .p128, .p132, .p136, .p140, .p144]
  | .trim => [.p260, .p264, .p268, .p272, .p276, .p280, .p284, .p288]
  | .input => [.p600, .p604, .p608, .p612, .p616, .p620, .p624, .p628]

def LoadSite.address (site : LoadSite) (s : ArmState) : BitVec 64 :=
  match site with
  | .identity => r (.GPR 1#5) s + (r (.GPR 9#5) s <<< 3)
  | .trim => r (.GPR 10#5) s + (r (.GPR 9#5) s <<< 3)
  | .input => r (.GPR 1#5) s + (r (.GPR 13#5) s <<< 3)

def loaded (site : LoadSite) (s : ArmState) (base value : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (site.start + 32))
    (w (.GPR site.destination) value (NatCompare.saved s site.scratch))

theorem load_run (site : LoadSite) (s : ArmState) (base value : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64)
    (separate : (site.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (site.address s).toNat)
    (valueAt : read_mem_bytes 8 (site.address s) s = value) :
    run 8 s = loaded site s base value := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s site.scratch) = r (.GPR site.scratch) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have observed : read_mem_bytes 8 (site.address s) (NatCompare.saved s site.scratch) = value := by
    unfold NatCompare.saved
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      physical (by bv_omega) (by bv_omega)]
    exact valueAt
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := pc
  have follows : Follows base site.ops s := by
    cases site <;> simp [LoadSite.ops, LoadSite.start, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = site.ops.length by cases site <;> rfl,
    block_run base site.ops s code error aligned follows]
  have effect : block base site.ops s =
      w .PC (read_pc s + 32#64) (w (.GPR site.destination) value (NatCompare.saved s site.scratch)) := by
    cases site with
    | identity =>
      change NatAdd.indexedReadSequence s 1#5 9#5 11#5 10#5 = _
      exact NatAdd.indexedReadSequence_eq s 1#5 9#5 11#5 10#5 value
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) observed restored
    | trim =>
      change NatAdd.indexedReadSequence s 10#5 9#5 12#5 11#5 = _
      exact NatAdd.indexedReadSequence_eq s 10#5 9#5 12#5 11#5 value
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) observed restored
    | input =>
      change NatAdd.indexedReadSequence s 1#5 13#5 9#5 17#5 = _
      exact NatAdd.indexedReadSequence_eq s 1#5 13#5 9#5 17#5 value
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) observed restored
  rw [effect]
  simp only [loaded, pc, BitVec.ofNat_add, BitVec.add_assoc]

end SszArm.NatMulWord
