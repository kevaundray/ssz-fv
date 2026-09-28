import SszArm.NatMulExec
import SszArm.NatAddLoadState
import SszArm.NatCompareBlocks

namespace SszArm.NatMul

inductive LoopLoadSite where
  | right | output
  deriving DecidableEq

def LoopLoadSite.start : LoopLoadSite → Nat
  | .right => 692 | .output => 724

def LoopLoadSite.pointer : LoopLoadSite → BitVec 5
  | .right => 8#5 | .output => 11#5

def LoopLoadSite.destination : LoopLoadSite → BitVec 5
  | .right => 18#5 | .output => 1#5

def LoopLoadSite.ops : LoopLoadSite → List Op
  | .right => [.p692, .p696, .p700, .p704, .p708, .p712, .p716, .p720]
  | .output => [.p724, .p728, .p732, .p736, .p740, .p744, .p748, .p752]

def LoopLoadSite.address (site : LoopLoadSite) (s : ArmState) : BitVec 64 :=
  r (.GPR site.pointer) s + (r (.GPR 16#5) s <<< 3)

def loopLoaded (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (site.start + 32))
    (w (.GPR site.destination) value (NatCompare.saved s 9#5))

theorem loop_load_run (site : LoopLoadSite) (s : ArmState) (base value : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (site.address s).toNat + 8 ≤ 2^64)
    (separate : (site.address s).toNat + 8 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (site.address s).toNat)
    (valueAt : read_mem_bytes 8 (site.address s) s = value) :
    run 8 s = loopLoaded site s base value := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have observed : read_mem_bytes 8 (site.address s) (NatCompare.saved s 9#5) = value := by
    unfold NatCompare.saved
    rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
      physical (by bv_omega) (by bv_omega)]
    exact valueAt
  have hpc : r .PC s = base + BitVec.ofNat 64 site.start := pc
  have follows : Follows base site.ops s := by
    cases site <;> simp [LoopLoadSite.ops, LoopLoadSite.start, Follows, Op.row, Op.effect,
      put, next, state_simp_rules, hpc, BitVec.add_assoc]
  rw [show 8 = site.ops.length by cases site <;> rfl,
    block_run base site.ops s code error aligned follows]
  have effect : block base site.ops s =
      w .PC (read_pc s + 32#64) (w (.GPR site.destination) value (NatCompare.saved s 9#5)) := by
    cases site with
    | right =>
      change NatAdd.indexedReadSequence s 8#5 16#5 9#5 18#5 = _
      exact NatAdd.indexedReadSequence_eq s 8#5 16#5 9#5 18#5 value
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) observed restored
    | output =>
      change NatAdd.indexedReadSequence s 11#5 16#5 9#5 1#5 = _
      exact NatAdd.indexedReadSequence_eq s 11#5 16#5 9#5 1#5 value
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) observed restored
  rw [effect]
  simp only [loopLoaded, pc, BitVec.ofNat_add, BitVec.add_assoc]

theorem loop_load_words_run (site : LoopLoadSite) (s : ArmState) (base : BitVec 64)
    (words : List (BitVec 64)) (index : Fin words.length)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 site.start)
    (source : NatCompare.Source s (r (.GPR site.pointer) s) words)
    (memory : NatCompare.Words s (r (.GPR site.pointer) s) words)
    (indexAt : r (.GPR 16#5) s = BitVec.ofNat 64 index.val) :
    run 8 s = loopLoaded site s base words[index] := by
  have bound := source.2.1
  have hi := index.isLt
  have address : (site.address s).toNat = (r (.GPR site.pointer) s).toNat + 8 * index.val := by
    simp only [LoopLoadSite.address, indexAt]
    bv_omega
  have addressEq : site.address s = r (.GPR site.pointer) s + BitVec.ofNat 64 (8 * index.val) := by
    simp only [LoopLoadSite.address, indexAt]
    bv_omega
  apply loop_load_run site s base words[index] code error aligned pc source.1
  · rw [address]; omega
  · rw [address]
    rcases source.2.2 with empty | apart
    · simp [empty] at hi
    · change (r (.GPR site.pointer) s).toNat + 8 * words.length ≤
          (r (.GPR 31#5) s).toNat - 16 ∨
          (r (.GPR 31#5) s).toNat ≤ (r (.GPR site.pointer) s).toNat at apart
      omega
  · rw [addressEq]
    exact memory index

end SszArm.NatMul
