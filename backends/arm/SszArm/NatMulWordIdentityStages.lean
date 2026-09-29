import SszArm.NatMulWordIdentityScan

namespace SszArm.NatMulWord

def identityCountOps : List Op := [.p160, .p164, .p168]
def identityCanonOps : List Op := [.p172, .p176]
def identityInitOps : List Op := [.p100, .p104]

theorem identity_count_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 160#64) : Follows base identityCountOps s := by
  have hpc : r .PC s = base + 160#64 := hp
  simp [identityCountOps, Follows, Op.row, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules, hpc, BitVec.add_assoc]

theorem identity_count_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base identityCountOps s) =
      if r (.GPR 8#5) s + 1#64 = 1#64 then base + 172#64 else base + 180#64 := by
  simp [identityCountOps, block, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem identity_count_pointer (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (block base identityCountOps s) = r (.GPR 1#5) s := by
  simp [identityCountOps, block, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem identity_count_payload (s : ArmState) (base : BitVec 64) :
    r (.GPR 2#5) (block base identityCountOps s) = r (.GPR 8#5) s + 1#64 := by
  simp [identityCountOps, block, Op.effect, put, next,
    Udivti3.compare, Udivti3.next, state_simp_rules]

theorem identity_canon_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 172#64) : Follows base identityCanonOps s := by
  have hpc : r .PC s = base + 172#64 := hp
  simp [identityCanonOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem identity_canon_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 172#64) :
    read_pc (block base identityCanonOps s) = base + 180#64 := by
  have hpc : r .PC s = base + 172#64 := hp
  simp [identityCanonOps, block, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem identity_canon_pointer (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (block base identityCanonOps s) = 0#64 := by
  simp [identityCanonOps, block, Op.effect, put, next, state_simp_rules]

theorem identity_canon_payload (s : ArmState) (base : BitVec 64) :
    r (.GPR 2#5) (block base identityCanonOps s) = read_mem_bytes 8 (r (.GPR 1#5) s) s := by
  simp [identityCanonOps, block, Op.effect, put, next, state_simp_rules]

theorem identity_init_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 100#64) (hn : r (.GPR 1#5) s ≠ 0#64) :
    Follows base identityInitOps s := by
  have hpc : r .PC s = base + 100#64 := hp
  simp [identityInitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, hn]

theorem identity_init_pc (s : ArmState) (base : BitVec 64)
    (hn : r (.GPR 1#5) s ≠ 0#64) :
    read_pc (block base identityInitOps s) = base + 108#64 := by
  simp [identityInitOps, block, Op.effect, put, next,
    state_simp_rules, hn, BitVec.add_assoc]

theorem identity_init_pointer (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (block base identityInitOps s) = r (.GPR 1#5) s := by
  simp [identityInitOps, block, Op.effect, put, next, state_simp_rules]

theorem identity_init_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base identityInitOps s) = r (.GPR 2#5) s - 1#64 := by
  simp [identityInitOps, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatMulWord
