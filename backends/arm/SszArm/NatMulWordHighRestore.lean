import SszArm.NatMulWordHighRun

namespace SszArm.NatMulWord

private theorem restore_put_memory (reg : BitVec 5) (value : BitVec 64) (s : ArmState) :
    (put reg value s).mem = s.mem := by
  simp only [put, next, ArmState.mem_w_eq_mem]

private theorem restore_put_read (reg : BitVec 5) (value : BitVec 64) (s : ArmState)
    (size : Nat) (address : BitVec 64) :
    read_mem_bytes size address (put reg value s) = read_mem_bytes size address s := by
  simp only [put, next, read_mem_bytes_of_w]

theorem high_restore_memory (site : HighSite) (s : ArmState) (base : BitVec 64) :
    (block base site.restoreOps s).mem = s.mem := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => t.mem) site.restoreOps s ?_
  intro op member t
  cases site <;>
    simp only [HighSite.restoreOps, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Op.effect, restore_put_memory]

private def restoreUpper : HighSite → List Op
  | .first => [.p564, .p568]
  | .loop => [.p720, .p724]
  | .small => [.p1012, .p1016]

private def restoreMiddle : HighSite → List Op
  | .first => [.p572, .p576]
  | .loop => [.p728, .p732]
  | .small => [.p1020, .p1024]

private def restoreLower : HighSite → List Op
  | .first => [.p580, .p584]
  | .loop => [.p736, .p740]
  | .small => [.p1028, .p1032]

private def restoreFinish : HighSite → Op
  | .first => .p588
  | .loop => .p744
  | .small => .p1036

private theorem restore_split (site : HighSite) (s : ArmState) (base : BitVec 64) :
    block base site.restoreOps s = (restoreFinish site).effect base
      (block base (restoreLower site)
        (block base (restoreMiddle site) (block base (restoreUpper site) s))) := by
  have ops : site.restoreOps = restoreUpper site ++ restoreMiddle site ++
      restoreLower site ++ [restoreFinish site] := by
    cases site <;> rfl
  simp only [block, ops, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem restore_pair_register_step (s t : ArmState)
    (reg firstReg secondReg : BitVec 5) (firstOffset secondOffset : BitVec 64)
    (first : put firstReg (read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s) s = t)
    (notSP : firstReg ≠ 31#5) :
    r (.GPR reg)
        (put secondReg (read_mem_bytes 8 (r (.GPR 31#5) t + secondOffset) t) t) =
      if reg = secondReg then read_mem_bytes 8 (r (.GPR 31#5) s + secondOffset) s
      else if reg = firstReg then read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s
      else r (.GPR reg) s := by
  have stack := high_put_gpr firstReg 31#5
    (read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s) s
  have memory := restore_put_read firstReg
    (read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s) s 8
  have observed := high_put_gpr firstReg reg
    (read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s) s
  rw [first] at stack memory observed
  rw [if_neg (Ne.symm notSP)] at stack
  rw [high_put_gpr, stack, memory, observed]

private theorem restore_pair_register (base : BitVec 64) (s : ArmState) (reg : BitVec 5)
    (first second : Op) (firstReg secondReg : BitVec 5)
    (firstOffset secondOffset : BitVec 64)
    (firstEffect : ∀ t, first.effect base t =
      put firstReg (read_mem_bytes 8 (r (.GPR 31#5) t + firstOffset) t) t)
    (secondEffect : ∀ t, second.effect base t =
      put secondReg (read_mem_bytes 8 (r (.GPR 31#5) t + secondOffset) t) t)
    (notSP : firstReg ≠ 31#5) :
    r (.GPR reg) (block base [first, second] s) =
      if reg = secondReg then read_mem_bytes 8 (r (.GPR 31#5) s + secondOffset) s
      else if reg = firstReg then read_mem_bytes 8 (r (.GPR 31#5) s + firstOffset) s
      else r (.GPR reg) s := by
  change r (.GPR reg) (second.effect base (first.effect base s)) = _
  exact (congrArg (fun t => r (.GPR reg) t) (secondEffect (first.effect base s))).trans
    (restore_pair_register_step s (first.effect base s) reg firstReg secondReg
      firstOffset secondOffset (firstEffect s).symm notSP)

private theorem restore_upper_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base (restoreUpper site) s) = r (.GPR 31#5) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR 31#5) t) (restoreUpper site) s ?_
  intro op member t
  cases site <;>
    simp only [restoreUpper, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals
    simp only [Op.effect, high_put_gpr] <;> arm_word_nf <;>
      simp (config := {decide := true}) only [↓reduceIte]

private theorem restore_middle_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base (restoreMiddle site) s) = r (.GPR 31#5) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR 31#5) t) (restoreMiddle site) s ?_
  intro op member t
  cases site <;>
    simp only [restoreMiddle, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals
    simp only [Op.effect, high_put_gpr] <;> arm_word_nf <;>
      simp (config := {decide := true}) only [↓reduceIte]

private theorem restore_lower_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base (restoreLower site) s) = r (.GPR 31#5) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.GPR 31#5) t) (restoreLower site) s ?_
  intro op member t
  cases site <;>
    simp only [restoreLower, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals
    simp only [Op.effect, high_put_gpr] <;> arm_word_nf <;>
      simp (config := {decide := true}) only [↓reduceIte]

private theorem restore_upper_read (site : HighSite) (s : ArmState) (base : BitVec 64)
    (size : Nat) (address : BitVec 64) :
    read_mem_bytes size address (block base (restoreUpper site) s) =
      read_mem_bytes size address s := by
  cases site <;>
    simp only [restoreUpper, block, List.foldl_cons, List.foldl_nil,
      Op.effect, restore_put_read]

private theorem restore_middle_read (site : HighSite) (s : ArmState) (base : BitVec 64)
    (size : Nat) (address : BitVec 64) :
    read_mem_bytes size address (block base (restoreMiddle site) s) =
      read_mem_bytes size address s := by
  cases site <;>
    simp only [restoreMiddle, block, List.foldl_cons, List.foldl_nil,
      Op.effect, restore_put_read]

private theorem restore_upper_register (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) (block base (restoreUpper site) s) =
      if reg = site.saved[4]! then read_mem_bytes 8 (r (.GPR 31#5) s + 32#64) s
      else if reg = site.saved[5]! then read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s
      else r (.GPR reg) s := by
  cases site with
  | first =>
    exact restore_pair_register base s reg .p564 .p568 15#5 13#5 40#64 32#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)
  | loop =>
    exact restore_pair_register base s reg .p720 .p724 14#5 13#5 40#64 32#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)
  | small =>
    exact restore_pair_register base s reg .p1012 .p1016 15#5 14#5 40#64 32#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)

private theorem restore_middle_register (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) (block base (restoreMiddle site) s) =
      if reg = site.saved[2]! then read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s
      else if reg = site.saved[3]! then read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s
      else r (.GPR reg) s := by
  cases site with
  | first =>
    exact restore_pair_register base s reg .p572 .p576 12#5 11#5 24#64 16#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)
  | loop =>
    exact restore_pair_register base s reg .p728 .p732 12#5 11#5 24#64 16#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)
  | small =>
    exact restore_pair_register base s reg .p1020 .p1024 13#5 12#5 24#64 16#64
      (by intro t; simp only [Op.effect]; arm_word_nf)
      (by intro t; simp only [Op.effect]; arm_word_nf) (by decide)

private theorem restore_lower_register (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) (block base (restoreLower site) s) =
      if reg = site.saved[0]! then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = site.saved[1]! then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else r (.GPR reg) s := by
  cases site with
  | first =>
    change r (.GPR reg) (block base [.p580, .p584] s) =
      if reg = 9#5 then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = 10#5 then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else r (.GPR reg) s
    simpa only [BitVec.add_zero] using
      restore_pair_register base s reg .p580 .p584 10#5 9#5 8#64 0#64
        (by intro t; simp only [Op.effect]; arm_word_nf)
        (by intro t; simp only [Op.effect, BitVec.add_zero]; arm_word_nf) (by decide)
  | loop =>
    change r (.GPR reg) (block base [.p736, .p740] s) =
      if reg = 9#5 then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = 10#5 then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else r (.GPR reg) s
    simpa only [BitVec.add_zero] using
      restore_pair_register base s reg .p736 .p740 10#5 9#5 8#64 0#64
        (by intro t; simp only [Op.effect]; arm_word_nf)
        (by intro t; simp only [Op.effect, BitVec.add_zero]; arm_word_nf) (by decide)
  | small =>
    change r (.GPR reg) (block base [.p1028, .p1032] s) =
      if reg = 10#5 then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = 11#5 then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else r (.GPR reg) s
    simpa only [BitVec.add_zero] using
      restore_pair_register base s reg .p1028 .p1032 11#5 10#5 8#64 0#64
        (by intro t; simp only [Op.effect]; arm_word_nf)
        (by intro t; simp only [Op.effect, BitVec.add_zero]; arm_word_nf) (by decide)

private theorem restore_finish_register (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) ((restoreFinish site).effect base s) =
      if reg = 31#5 then r (.GPR 31#5) s + 48#64 else r (.GPR reg) s := by
  cases site <;> simp only [restoreFinish, Op.effect, high_put_gpr] <;> arm_word_nf

private theorem restore_register_chain (site : HighSite) (s upper middle lower : ArmState)
    (base : BitVec 64) (reg : BitVec 5)
    (upperEq : block base (restoreUpper site) s = upper)
    (middleEq : block base (restoreMiddle site) upper = middle)
    (lowerEq : block base (restoreLower site) middle = lower) :
    r (.GPR reg) ((restoreFinish site).effect base lower) =
      if reg = 31#5 then r (.GPR 31#5) s + 48#64
      else if reg = site.saved[0]! then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = site.saved[1]! then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else if reg = site.saved[2]! then read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s
      else if reg = site.saved[3]! then read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s
      else if reg = site.saved[4]! then read_mem_bytes 8 (r (.GPR 31#5) s + 32#64) s
      else if reg = site.saved[5]! then read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s
      else r (.GPR reg) s := by
  have upperStack := restore_upper_stack site s base
  have upperRead := restore_upper_read site s base
  have upperRegister := restore_upper_register site s base reg
  rw [upperEq] at upperStack upperRead upperRegister
  have middleStack := restore_middle_stack site upper base
  have middleRead := restore_middle_read site upper base
  have middleRegister := restore_middle_register site upper base reg
  rw [middleEq] at middleStack middleRead middleRegister
  have lowerStack := restore_lower_stack site middle base
  have lowerRegister := restore_lower_register site middle base reg
  rw [lowerEq] at lowerStack lowerRegister
  rw [restore_finish_register, lowerStack, middleStack, upperStack,
    lowerRegister, middleRegister, upperRegister]
  simp only [middleStack, upperStack, middleRead, upperRead]

private theorem restore_register (site : HighSite) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.GPR reg) (block base site.restoreOps s) =
      if reg = 31#5 then r (.GPR 31#5) s + 48#64
      else if reg = site.saved[0]! then read_mem_bytes 8 (r (.GPR 31#5) s) s
      else if reg = site.saved[1]! then read_mem_bytes 8 (r (.GPR 31#5) s + 8#64) s
      else if reg = site.saved[2]! then read_mem_bytes 8 (r (.GPR 31#5) s + 16#64) s
      else if reg = site.saved[3]! then read_mem_bytes 8 (r (.GPR 31#5) s + 24#64) s
      else if reg = site.saved[4]! then read_mem_bytes 8 (r (.GPR 31#5) s + 32#64) s
      else if reg = site.saved[5]! then read_mem_bytes 8 (r (.GPR 31#5) s + 40#64) s
      else r (.GPR reg) s := by
  exact (congrArg (fun t => r (.GPR reg) t) (restore_split site s base)).trans
    (restore_register_chain site s
      (block base (restoreUpper site) s)
      (block base (restoreMiddle site) (block base (restoreUpper site) s))
      (block base (restoreLower site)
        (block base (restoreMiddle site) (block base (restoreUpper site) s)))
      base reg rfl rfl rfl)

theorem high_restore_stack (site : HighSite) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base site.restoreOps s) = r (.GPR 31#5) s + 48#64 := by
  exact (restore_register site s base 31#5).trans (if_pos rfl)

theorem high_restore_read (site : HighSite) (s : ArmState) (base : BitVec 64)
    (index : Fin 6) :
    r (.GPR site.saved[index.val]!) (block base site.restoreOps s) =
      read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (8 * index.val)) s := by
  rw [restore_register]
  rcases index with ⟨index, bound⟩
  have indices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 := by
    omega
  rcases indices with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases site <;> simp (config := {decide := true}) [HighSite.saved]

end SszArm.NatMulWord
