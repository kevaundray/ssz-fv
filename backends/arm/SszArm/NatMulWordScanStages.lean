import SszArm.NatMulWordScanFrame
import SszArm.DelimitedArenaArithmetic

namespace SszArm.NatMulWord

/-- Opaque checkpoint projections avoid re-expanding a complete loop state. -/
@[simp] theorem loaded_pc (site : LoadSite) (s : ArmState) (base word : BitVec 64) :
    read_pc (loaded site s base word) = base + BitVec.ofNat 64 (site.start + 32) := by
  simp [loaded, state_simp_rules]

@[simp] theorem loaded_value (site : LoadSite) (s : ArmState) (base word : BitVec 64) :
    r (.GPR site.destination) (loaded site s base word) = word := by
  simp [loaded, state_simp_rules]

theorem loaded_register (site : LoadSite) (s : ArmState) (base word : BitVec 64)
    (reg : BitVec 5) (hne : reg ≠ site.destination) :
    r (.GPR reg) (loaded site s base word) = r (.GPR reg) s := by
  simp [loaded, NatCompare.saved, state_simp_rules, hne]

def identityGuard : List Op := [.p108, .p112]
def identityTail : List Op := [.p148, .p152, .p156]
def trimGuard : List Op := [.p252, .p256]
def trimTail : List Op := [.p292, .p296, .p300]

def identityRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base identityTail (loaded .identity (block base identityGuard s) base word)

def trimRound (s : ArmState) (base word : BitVec 64) : ArmState :=
  block base trimTail (loaded .trim (block base trimGuard s) base word)

theorem identity_guard_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 108#64) : Follows base identityGuard s := by
  have hpc : r .PC s = base + 108#64 := hp
  simp [identityGuard, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem identity_guard_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base identityGuard s) = r (.GPR reg) s := by
  simp [identityGuard, block, Op.effect, put, next, state_simp_rules]

theorem identity_guard_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base identityGuard s) =
      if r (.GPR 9#5) s + 1#64 = 0#64 then base + 832#64 else base + 116#64 := by
  simp [identityGuard, block, Op.effect, put, next, state_simp_rules]

theorem trim_guard_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 252#64) : Follows base trimGuard s := by
  have hpc : r .PC s = base + 252#64 := hp
  simp [trimGuard, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem trim_guard_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.GPR reg) (block base trimGuard s) = r (.GPR reg) s := by
  simp [trimGuard, block, Op.effect, put, next, state_simp_rules]

theorem trim_guard_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base trimGuard s) =
      if r (.GPR 2#5) s + r (.GPR 9#5) s = 0#64 then base + 920#64 else base + 260#64 := by
  simp [trimGuard, block, Op.effect, put, next, state_simp_rules, Delimited.add_zero_flag]

theorem identity_tail_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 148#64) : Follows base identityTail s := by
  have hpc : r .PC s = base + 148#64 := hp
  simp [identityTail, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem identity_tail_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) :
    r (.GPR reg) (block base identityTail s) = r (.GPR reg) s := by
  simp [identityTail, block, Op.effect, put, next, state_simp_rules, h8, h9]

theorem identity_tail_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base identityTail s) = r (.GPR 9#5) s - 1#64 := by
  simp [identityTail, block, Op.effect, put, next, state_simp_rules]

theorem identity_tail_count (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (block base identityTail s) = r (.GPR 9#5) s := by
  simp [identityTail, block, Op.effect, put, next, state_simp_rules]

theorem identity_tail_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base identityTail s) =
      if r (.GPR 10#5) s = 0#64 then base + 108#64 else base + 160#64 := by
  simp [identityTail, block, Op.effect, put, next, state_simp_rules]

theorem trim_tail_follows (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 292#64) : Follows base trimTail s := by
  have hpc : r .PC s = base + 292#64 := hp
  simp [trimTail, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem trim_tail_keep (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (h8 : reg ≠ 8#5) (h9 : reg ≠ 9#5) :
    r (.GPR reg) (block base trimTail s) = r (.GPR reg) s := by
  simp [trimTail, block, Op.effect, put, next, state_simp_rules, h8, h9]

theorem trim_tail_index (s : ArmState) (base : BitVec 64) :
    r (.GPR 9#5) (block base trimTail s) = r (.GPR 9#5) s - 1#64 := by
  simp [trimTail, block, Op.effect, put, next, state_simp_rules]

theorem trim_tail_offset (s : ArmState) (base : BitVec 64) :
    r (.GPR 8#5) (block base trimTail s) = r (.GPR 8#5) s + 8#64 := by
  simp [trimTail, block, Op.effect, put, next, state_simp_rules]

theorem trim_tail_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base trimTail s) =
      if r (.GPR 11#5) s = 0#64 then base + 252#64 else base + 304#64 := by
  simp [trimTail, block, Op.effect, put, next, state_simp_rules]

end SszArm.NatMulWord
