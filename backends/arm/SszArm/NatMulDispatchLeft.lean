import SszArm.NatMulScanRight

namespace SszArm.NatMul

open SszNative.Limbs

/-- The left phase's actual join: an immediate right skips the right scan;
a borrowed right is scanned even when the left is zero. -/
def LeftDispatch (s t : ArmState) (base : BitVec 64) (words : List (BitVec 64)) : Prop :=
  if r (.GPR 3#5) s = 0#64 then
    read_pc t = base + (if sigWords words = 0 ∨ r (.GPR 4#5) s = 0#64 then 264#64 else 228#64)
  else
    r (.GPR 21#5) t = BitVec.ofNat 64 (sigWords words) ∧
    r (.GPR 8#5) t = r (.GPR 2#5) s ∧ read_pc t = base + 160#64

theorem left_dispatch (s : ArmState) (base : BitVec 64) (words : List (BitVec 64))
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 28#64)
    (ho : NatCompare.Operand s (r (.GPR 1#5) s) (r (.GPR 2#5) s) words) :
    ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧ LeftDispatch s t base words := by
  by_cases small : r (.GPR 1#5) s = 0#64
  · have representation := ho.small small
    subst words
    let ops : List Op :=
      if r (.GPR 2#5) s = 0#64 then
        if r (.GPR 3#5) s = 0#64 then [.p28, .p104, .p148]
        else [.p28, .p104, .p148, .p152, .p156]
      else if r (.GPR 3#5) s = 0#64 then
        if r (.GPR 4#5) s = 0#64 then [.p28, .p104, .p108, .p140, .p144]
        else [.p28, .p104, .p108, .p140]
      else [.p28, .p104, .p108, .p112, .p116, .p120]
    let t := block base ops s
    have hpc : r .PC s = base + 28#64 := hp
    have follows : Follows base ops s := by
      by_cases lzero : r (.GPR 2#5) s = 0#64 <;>
        by_cases rsmall : r (.GPR 3#5) s = 0#64 <;>
        by_cases rzero : r (.GPR 4#5) s = 0#64 <;>
        simp [ops, lzero, rsmall, rzero, Follows, Op.row, Op.effect, put, next,
          state_simp_rules, hpc, small, BitVec.add_assoc]
    refine ⟨ops.length, t, block_run base ops s hc he ha follows,
      scan_pure_frame base ops s (by
        dsimp only [ops]; split <;> split <;> (try split) <;> decide), ?_⟩
    by_cases lzero : r (.GPR 2#5) s = 0#64 <;>
      by_cases rsmall : r (.GPR 3#5) s = 0#64 <;>
      by_cases rzero : r (.GPR 4#5) s = 0#64 <;>
      simp [LeftDispatch, t, ops, lzero, rsmall, rzero, sigWords, significantCount,
        block, Op.effect, put, next, state_simp_rules, hpc, small, BitVec.add_assoc]
  · obtain ⟨length, source, memory⟩ := ho.large small
    have payload : r (.GPR 2#5) s = BitVec.ofNat 64 words.length := by
      rw [← length, BitVec.ofNat_toNat]
    obtain ⟨fuel, u, hu, huf, count, index, raw, pc⟩ := left_large_scan s base
      (r (.GPR 1#5) s) words hc he ha hp rfl small payload source memory
    by_cases rsmall : r (.GPR 3#5) s = 0#64
    · have bound : sigWords words < 2^64 :=
        Nat.lt_of_le_of_lt (sigWords_le_length words) ho.length_bound
      have czero : (BitVec.ofNat 64 (sigWords words) = 0#64) ↔ sigWords words = 0 := by
        constructor <;> intro h <;> bv_omega
      let ops : List Op := if sigWords words = 0 then [.p136]
        else if r (.GPR 4#5) s = 0#64 then [.p136, .p140, .p144] else [.p136, .p140]
      let t := block base ops u
      have hpc : r .PC u = base + 136#64 := by simpa [rsmall] using pc
      have h4 := huf.registers 4#5 (by decide)
      have follows : Follows base ops u := by
        by_cases zero : sigWords words = 0 <;> by_cases rzero : r (.GPR 4#5) s = 0#64 <;>
          simp [ops, zero, rzero, Follows, Op.row, Op.effect, put, next,
            state_simp_rules, hpc, index, czero, h4, BitVec.add_assoc]
      have ht := block_run base ops u (huf.code hc) (huf.error.trans he) (huf.aligned ha) follows
      have htf : ScanFrame u t := scan_pure_frame base ops u (by
        dsimp only [ops]; split <;> (try split) <;> decide)
      refine ⟨fuel + ops.length, t, ?_, huf.trans htf, ?_⟩
      · rw [run_plus, hu, ht]
      · by_cases zero : sigWords words = 0 <;> by_cases rzero : r (.GPR 4#5) s = 0#64 <;>
          simp [LeftDispatch, t, ops, rsmall, zero, rzero, block, Op.effect, put, next,
            state_simp_rules, hpc, index, czero, h4, BitVec.add_assoc]
    · refine ⟨fuel, u, hu, huf, ?_⟩
      simpa [LeftDispatch, rsmall] using And.intro count (And.intro raw pc)

end SszArm.NatMul
