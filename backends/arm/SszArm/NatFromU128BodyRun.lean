import SszArm.NatFromU128Bodies

namespace SszArm.NatFromU128

private theorem follows_append (base : BitVec 64) (a b : List Op) (s : ArmState)
    (ha : Follows base a s) (hb : Follows base b (block base a s)) :
    Follows base (a ++ b) s := by
  induction a generalizing s with
  | nil => exact hb
  | cons op ops ih => exact ⟨ha.1, ih _ ha.2 hb⟩

private theorem lower_follows (kind : LowerKind) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.entry) : Follows base kind.ops s := by
  have hpc : r .PC s = base + BitVec.ofNat 64 kind.entry := hp
  cases kind <;>
    simp [LowerKind.ops, LowerKind.entry, Follows, Op.row, Op.effect, put, next,
      state_simp_rules, hpc, BitVec.add_assoc]

private theorem lower_follows_append (kind : LowerKind) (rest : List Op)
    (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (hf : Follows base rest (block base kind.ops s)) :
    Follows base (kind.ops ++ rest) s :=
  follows_append base kind.ops rest s (lower_follows kind s base hp) hf

/-- Each lowering chunk is opaque between its entry and exit; the only
remaining concrete runs are the two/five instruction straight-line chunks. -/
theorem body_run (body : Body) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 body.entry) (space : Space s) :
    run body.ops.length s = body.final s := by
  rw [← body_effect body s base space]
  apply block_run base body.ops s hc he ha
  have hpc : r .PC s = base + BitVec.ofNat 64 body.entry := hp
  cases body
  · change Follows base (LowerKind.smallPair.ops ++ LowerKind.smallStatus.ops ++ [.p84]) s
    rw [List.append_assoc]
    apply lower_follows_append .smallPair _ s base hp
    let a := block base LowerKind.smallPair.ops s
    have sa : Space a := lower_space .smallPair s base space
    have pa : read_pc a = base + 44#64 := by
      rw [lower_pc .smallPair s base space, hp]
      simp [Body.entry, LowerKind.ops, BitVec.add_assoc]
    apply lower_follows_append .smallStatus _ a base pa
    have pb : read_pc (block base LowerKind.smallStatus.ops a) = base + 84#64 := by
      rw [lower_pc .smallStatus a base sa, pa]
      simp [LowerKind.ops, BitVec.add_assoc]
    simpa [Follows, Op.row] using And.intro pb True.intro
  · change Follows base ([.p220, .p224] ++ LowerKind.zero48.ops ++ LowerKind.zero32.ops ++
      LowerKind.zero16.ops ++ LowerKind.errorPair.ops ++ [.p412, .p416]) s
    simp only [List.append_assoc]
    apply follows_append base [.p220, .p224] _ s
    · simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, Body.entry,
        BitVec.add_assoc]
    · let a := block base [.p220, .p224] s
      have sa : Space a := by
        constructor
        · simpa [a, block, Op.effect, put, next, state_simp_rules] using space.stack
        · simpa [a, block, Op.effect, put, next, state_simp_rules] using space.output
        · simpa [a, block, Op.effect, put, next, state_simp_rules] using space.separate
      have pa : read_pc a = base + 228#64 := by
        simp [a, block, Op.effect, put, next, state_simp_rules, hpc, Body.entry, BitVec.add_assoc]
      apply lower_follows_append .zero48 _ a base pa
      let b := block base LowerKind.zero48.ops a
      have sb : Space b := lower_space .zero48 a base sa
      have pb : read_pc b = base + 276#64 := by
        rw [lower_pc .zero48 a base sa, pa]
        simp [LowerKind.ops, BitVec.add_assoc]
      apply lower_follows_append .zero32 _ b base pb
      let c := block base LowerKind.zero32.ops b
      have sc : Space c := lower_space .zero32 b base sb
      have pc : read_pc c = base + 324#64 := by
        rw [lower_pc .zero32 b base sb, pb]
        simp [LowerKind.ops, BitVec.add_assoc]
      apply lower_follows_append .zero16 _ c base pc
      let d := block base LowerKind.zero16.ops c
      have sd : Space d := lower_space .zero16 c base sc
      have pd : read_pc d = base + 372#64 := by
        rw [lower_pc .zero16 c base sc, pc]
        simp [LowerKind.ops, BitVec.add_assoc]
      apply lower_follows_append .errorPair _ d base pd
      have pe : read_pc (block base LowerKind.errorPair.ops d) = base + 412#64 := by
        rw [lower_pc .errorPair d base sd, pd]
        simp [LowerKind.ops, BitVec.add_assoc]
      change r .PC _ = _ at pe
      simp [Follows, Op.row, Op.effect, next, state_simp_rules, pe, BitVec.add_assoc]
  · change Follows base ([.p156, .p160, .p164, .p168, .p172] ++
      LowerKind.wideStatus.ops ++ [.p216]) s
    rw [List.append_assoc]
    apply follows_append base [.p156, .p160, .p164, .p168, .p172] _ s
    · simp [Follows, Op.row, Op.effect, put, next, state_simp_rules, hpc, Body.entry,
        BitVec.add_assoc]
    · let a := block base [.p156, .p160, .p164, .p168, .p172] s
      have sa : Space a := by
        rw [show a = _ from commit_effect s base]
        constructor
        · simpa [commitMemory, state_simp_rules] using space.stack
        · simpa [commitMemory, state_simp_rules] using space.output
        · simpa [commitMemory, state_simp_rules] using space.separate
      have pa : read_pc a = base + 176#64 := by
        rw [show a = _ from commit_effect s base]
        simp [state_simp_rules, hpc, Body.entry, BitVec.add_assoc]
      apply lower_follows_append .wideStatus _ a base pa
      have pb : read_pc (block base LowerKind.wideStatus.ops a) = base + 216#64 := by
        rw [lower_pc .wideStatus a base sa, pa]
        simp [LowerKind.ops, BitVec.add_assoc]
      simpa [Follows, Op.row] using And.intro pb True.intro

end SszArm.NatFromU128
