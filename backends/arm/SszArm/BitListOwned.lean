import SszArm.BitListMemory

namespace SszArm.BitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open BitVector (Covers)

theorem option_bound {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : (helperOption s kind).toNat + 24 ≤ 2^64 := by
  have high := owned.stackHigh
  have descriptor := owned.descriptorBound
  cases kind <;> simp only [helperOption, optionAddress, Variant.descriptorBytes] at * <;> bv_omega

theorem original_option_bound {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : (optionAddress s kind).toNat + 24 ≤ 2^64 := by
  have descriptor := owned.descriptorBound
  cases kind <;> simp only [optionAddress, Variant.descriptorBytes] at * <;> bv_omega

theorem original_option_owned {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) :
    Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
      (optionAddress s kind).toNat 24 := by
  cases kind with
  | list => exact owned.descriptorOwned
  | progressive =>
    have address : (optionAddress s .progressive).toNat = (r (.GPR 1#5) s).toNat + 8 := by
      have bound := owned.descriptorBound
      simp only [Variant.descriptorBytes] at bound
      simp only [optionAddress]
      bv_omega
    rw [address]
    exact owned.descriptorOwned.subspan 8 24 (by decide)

theorem copied_option_owned {s : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s .list limit data) (base : BitVec 64) :
    Protected (Delimited.writesFor (called s base .list)
      (SszNative.Delimited.allocation data (arenaOf s)))
      (helperOption s .list).toNat 24 := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have address : (helperOption s .list).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    simp only [helperOption]
    bv_omega
  have output := owned.outputStack
  rcases output with empty | output
  · omega
  have outputApart := output ((r (.GPR 31#5) s).toNat - 112, 480) (by simp)
  have arenaApart : (r (.GPR 19#5) s).toNat + 24 ≤ (r (.GPR 31#5) s).toNat + 144 ∨
      (r (.GPR 31#5) s).toNat + 168 ≤ (r (.GPR 19#5) s).toNat := by
    rcases owned.arenaLocal with empty | separate
    · omega
    · have apart := separate ((r (.GPR 31#5) s).toNat + 144, 24) (by simp [localWrites, stackWrites])
      simpa using apart
  have locals : Protected (Delimited.localWrites (called s base .list)) (helperOption s .list).toNat 24 := by
    right
    intro span member
    simp only [Delimited.localWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [called_out, address]
      omega
    · simp only [Delimited.activationSpan, called_length, called_sp, helperSP, address]
      split <;> omega
  cases allocation : SszNative.Delimited.allocation data (arenaOf s) with
  | none => exact locals
  | some reservation =>
    right
    intro span member
    simp only [Delimited.writesFor, Delimited.allocatedWrites, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, called_arena] at member
    rcases member with member | rfl | rfl
    · exact (locals.resolve_left (by decide)) span member
    · rw [address]
      omega
    · have fresh := owned.fresh reservation allocation
      rcases fresh with empty | separate
      · omega
      · have apart := separate ((r (.GPR 31#5) s).toNat + 144, 24)
          (by simp [localWrites, stackWrites])
        rw [address]
        omega

theorem helper_option {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    SszNative.NatMemory.OptionAt (widthLoad (called s base kind)) (helperOption s kind).toNat limit := by
  cases kind with
  | progressive =>
    have observe : widthLoad (called s base .progressive) = widthLoad s := by
      funext address bytes
      simp only [widthLoad, called, progressiveCalled, BoolCodec.returned, state_simp_rules]
    simpa only [observe, Descriptor, helperOption] using owned.descriptor
  | list =>
    cases limit with
    | none => exact False.elim owned.descriptor
    | some cap =>
      have frame := called_frame owned base
      have preserved := frame.pair _ _ cap owned.descriptor (by
        intro nonzero countNonzero
        exact (local_covered s .list _).protected (owned.limbsOwned cap rfl nonzero countNonzero))
      have copied := copied_words owned base
      have pointer : widthLoad (called s base .list) ((helperOption s .list).toNat + 8) 8 =
          some (read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s).toNat := by
        simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (fun x : BitVec 64 => some x.toNat) copied.2.1
      have payload : widthLoad (called s base .list) ((helperOption s .list).toNat + 8 + 8) 8 =
          some (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s).toNat := by
        simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          BitVec.add_assoc, show 8#64 + 8#64 = 16#64 by decide] using
          congrArg (fun x : BitVec 64 => some x.toNat) copied.2.2
      apply (SszNative.NatMemory.option_some_iff_pair _ _ _ _ _ pointer payload).mpr
      refine ⟨?_, preserved⟩
      simpa only [widthLoad, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_ofNat] using congrArg (fun x : BitVec 32 => some x.toNat) copied.1

theorem helper_option_owned {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    Delimited.OptionOwned (Delimited.writesFor (called s base kind)
      (SszNative.Delimited.allocation data (arenaOf s)))
      (called s base kind) (helperOption s kind) limit := by
  have cover := helper_writes owned base (SszNative.Delimited.allocation data (arenaOf s))
  have header : Protected (Delimited.writesFor (called s base kind)
      (SszNative.Delimited.allocation data (arenaOf s))) (helperOption s kind).toNat 24 := by
    cases kind with
    | list => exact copied_option_owned owned base
    | progressive => exact cover.protected (original_option_owned owned)
  cases limit with
  | none => exact header
  | some cap =>
    refine ⟨header, ?_⟩
    have pointer : read_mem_bytes 8 (helperOption s kind + 8#64) (called s base kind) =
        read_mem_bytes 8 (optionAddress s kind + 8#64) s := by
      cases kind with
      | list => exact (copied_words owned base).2.1
      | progressive => simp [helperOption, called, progressiveCalled, BoolCodec.returned, state_simp_rules]
    have payload : read_mem_bytes 8 (helperOption s kind + 16#64) (called s base kind) =
        read_mem_bytes 8 (optionAddress s kind + 16#64) s := by
      cases kind with
      | list => exact (copied_words owned base).2.2
      | progressive => simp [helperOption, called, progressiveCalled, BoolCodec.returned, state_simp_rules]
    rw [pointer, payload]
    intro nonzero countNonzero
    exact cover.protected (owned.limbsOwned cap rfl nonzero countNonzero)

/-- No helper-result assumption: each ownership field follows from original
caller storage, the actual Some copy, or restoration before the true tail B. -/
theorem helper_owned {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    Delimited.Owned (called s base kind) limit data := by
  have frame := called_frame owned base
  have resources := called_resources owned base
  have locals := helper_locals owned base
  have low := owned.stackLow
  have high := owned.stackHigh
  have upper : (r (.GPR 31#5) s + 368#64).toNat = (r (.GPR 31#5) s).toNat + 368 := by bv_omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [called_length] using owned.length
  · simpa only [called_source] using owned.inputBound
  · rw [called_source]
    exact frame.bytes _ _ owned.inputBound ((local_covered s kind _).protected owned.inputOwned) owned.input
  · rw [called_option]
    exact option_bound owned
  · rw [called_option]
    exact helper_option owned base
  · rw [called_out]
    have output := owned.outputBound
    omega
  · simp only [Delimited.activationSpan, called_length, called_sp]
    cases kind <;> simp only [helperSP, upper] <;> split <;> omega
  · rw [called_out]
    have cover : Covers [((r (.GPR 31#5) s).toNat - 112, 480)]
        [Delimited.activationSpan (called s base kind)] := by
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      refine ⟨((r (.GPR 31#5) s).toNat - 112, 480), by simp, ?_, ?_⟩
      all_goals
        simp only [Delimited.activationSpan, called_length, called_sp]
        cases kind <;> simp only [helperSP, upper] <;> split <;> omega
    exact cover.protected (by simpa using owned.outputStack.subspan 0 76 (by decide))
  · simpa only [called_arena] using owned.arenaBound
  · simpa only [resources] using owned.arenaStorage
  · simpa only [resources] using owned.arenaNonnull
  · rw [called_arena]
    exact locals.protected owned.arenaLocal
  · intro reservation allocated
    rw [resources] at allocated
    have cover : Covers (localWrites s kind ++ [((r (.GPR 19#5) s).toNat, 24)])
        (Delimited.localWrites (called s base kind) ++ [((r (.GPR 4#5) (called s base kind)).toNat, 24)]) := by
      intro span member
      simp only [List.mem_append, List.mem_singleton, called_arena] at member
      rcases member with member | rfl
      · obtain ⟨outer, outerMember, left, right⟩ := locals span member
        exact ⟨outer, List.mem_append_left _ outerMember, left, right⟩
      · exact ⟨((r (.GPR 19#5) s).toNat, 24), by simp, Nat.le_refl _, Nat.le_refl _⟩
    exact cover.protected (owned.fresh reservation allocated)
  · rw [resources, called_source]
    exact (helper_writes owned base _).protected owned.inputOwned
  · rw [resources, called_option]
    exact helper_option_owned owned base

end SszArm.BitList
