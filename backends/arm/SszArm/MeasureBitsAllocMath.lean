import SszArm.MeasureBitsAllocGuards

namespace SszArm.Measure.Bits.Alloc

private theorem cmn_hi_zero (a b : BitVec 64) :
    ((AddWithCarry a b 0#1).2.c = 1#1 ∧ (AddWithCarry a b 0#1).2.z = 0#1) ↔
      2^64 < a.toNat + b.toNat := by
  have zero : (AddWithCarry a b 0#1).2.z = 0#1 ↔
      (AddWithCarry a b 0#1).2.z ≠ 1#1 := by bv_omega
  rw [zero]
  exact Delimited.cmn_hi a b

theorem address_exit (site : Site) (s : ArmState) (base : BitVec 64) :
    let pointer := read_mem_bytes 8 (r (.GPR 20#5) s) s
    let used := read_mem_bytes 8 (r (.GPR 20#5) s + 16#64) s
    let t := block site base CheckKind.address.ops s
    r (.GPR site.baseReg) t = pointer ∧ r (.GPR site.usedReg) t = used ∧
      r (.GPR site.workReg) t = used + pointer ∧
      read_pc t = if 2^64 ≤ used.toNat + pointer.toNat then base + 3528#64
        else base + BitVec.ofNat 64 (site.entry + 16) := by
  cases site <;>
    simp [block, CheckKind.ops, effect, put, next, Site.baseReg, Site.usedReg,
      Site.workReg, Site.tempReg, state_simp_rules, Udivti3.adc_carry, Udivti3.radix]

theorem round_exit (site : Site) (s : ArmState) (base : BitVec 64) :
    read_pc (block site base CheckKind.round.ops s) =
      if 2^64 < (r (.GPR site.workReg) s).toNat + 8 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 24) := by
  cases site <;> simp [block, CheckKind.ops, effect, put, next,
    state_simp_rules, cmn_hi_zero]

theorem align_exit (site : Site) (s : ArmState) (base : BitVec 64) :
    let rounded := (r (.GPR site.workReg) s + 7#64) &&& 18446744073709551608#64
    let padding := rounded - r (.GPR site.workReg) s
    let t := block site base CheckKind.align.ops s
    r (.GPR site.tempReg) t = rounded ∧
      r (.GPR site.usedReg) t = padding + r (.GPR site.usedReg) s ∧
      read_pc t = if 2^64 ≤ padding.toNat + (r (.GPR site.usedReg) s).toNat
        then base + 3528#64 else base + BitVec.ofNat 64 (site.entry + 44) := by
  cases site <;>
    simp [block, CheckKind.ops, effect, put, next, Site.baseReg, Site.usedReg,
      Site.workReg, Site.tempReg, state_simp_rules, Udivti3.adc_carry, Udivti3.radix]

theorem finish_exit (site : Site) (s : ArmState) (base : BitVec 64) :
    read_pc (block site base CheckKind.finish.ops s) =
      if 2^64 < (r (.GPR site.usedReg) s).toNat + 17 then base + 3528#64
      else base + BitVec.ofNat 64 (site.entry + 52) := by
  cases site <;> simp [block, CheckKind.ops, effect, put, next,
    state_simp_rules, cmn_hi_zero]

private theorem cmp_hi_ne (a b : BitVec 64) :
    ((AddWithCarry a (~~~b) 1#1).2.c = 1#1 ∧ a ≠ b) ↔ b.toNat < a.toNat := by
  simpa only [Udivti3.cmp_nonzero] using Udivti3.cmp_high a b

theorem capacity_exit (site : Site) (s : ArmState) (base : BitVec 64) :
    let capacity := read_mem_bytes 8 (r (.GPR 20#5) s + 8#64) s
    let finish := r (.GPR site.usedReg) s + 16#64
    let t := block site base CheckKind.capacity.ops s
    r (.GPR site.tempReg) t = capacity ∧ r (.GPR site.workReg) t = finish ∧
      read_pc t = if capacity.toNat < finish.toNat then base + 3528#64
        else base + BitVec.ofNat 64 (site.entry + 68) := by
  cases site <;>
    simp [block, CheckKind.ops, effect, put, next, Site.baseReg, Site.usedReg,
      Site.workReg, Site.tempReg, Udivti3.compare, Udivti3.next,
      state_simp_rules, cmp_hi_ne]

end SszArm.Measure.Bits.Alloc
