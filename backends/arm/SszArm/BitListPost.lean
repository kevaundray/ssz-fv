import SszArm.BitListOwned

namespace SszArm.BitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open BitVector (Covers)

theorem result_relocate (observe : Nat → Nat → Option Nat) (out source oldAddress newAddress : Nat)
    (data : Ssz.Bytes) (result : SszNative.Delimited.Outcome)
    (pointer : observe (oldAddress + 8) 8 = observe (newAddress + 8) 8)
    (payload : observe (oldAddress + 16) 8 = observe (newAddress + 16) 8)
    (observed : SszNative.Delimited.ResultAt observe out source oldAddress data result) :
    SszNative.Delimited.ResultAt observe out source newAddress data result := by
  cases outcome : result.result with
  | ok value => simpa only [SszNative.Delimited.ResultAt, outcome] using observed
  | error reason =>
    cases reason with
    | scratchExhausted => simpa only [SszNative.Delimited.ResultAt, outcome] using observed
    | semantic reason =>
      cases reason <;> simpa only [SszNative.Delimited.ResultAt, outcome, pointer, payload] using observed

theorem arena_readonly {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) :
    Protected (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s)))
      (r (.GPR 19#5) s).toNat 16 := by
  have initial := owned.arenaLocal.subspan 0 16 (by decide)
  cases allocation : SszNative.Delimited.allocation data (arenaOf s) with
  | none => simpa only [writesFor, Nat.add_zero] using initial
  | some reservation =>
    right
    intro span member
    simp only [writesFor, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with member | rfl | rfl
    · have separate := (initial.resolve_left (by decide)) span member
      simpa using separate
    · left
      omega
    · have fresh := owned.fresh reservation allocation
      rcases fresh with empty | separate
      · omega
      · have apart := separate ((r (.GPR 19#5) s).toNat, 24) (by simp)
        omega

theorem called_words {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (base : BitVec 64) :
    read_mem_bytes 8 (helperOption s kind + 8#64) (called s base kind) =
      read_mem_bytes 8 (optionAddress s kind + 8#64) s ∧
    read_mem_bytes 8 (helperOption s kind + 16#64) (called s base kind) =
      read_mem_bytes 8 (optionAddress s kind + 16#64) s := by
  cases kind with
  | list => exact (copied_words owned base).2
  | progressive => simp [helperOption, called, progressiveCalled, BoolCodec.returned, state_simp_rules]

theorem activation_from_frame {s t : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s .list limit data)
    (frame : MemoryFrame (writesFor s .list (SszNative.Delimited.allocation data (arenaOf s))) s t) :
    BoolCodec.ActivationPreserved s t := by
  intro index within
  change t.mem _ = s.mem _
  apply frame.protected_byte (owned.activationOwned rfl)
  · have bound := owned.stackHigh
    bv_omega
  · have bound := owned.stackHigh
    bv_omega

/-- The helper's committed effects are composed with the actual Some copy.
Final epilogues are memory-free; tail helpers may reuse the old activation. -/
theorem helper_post_frame {s t u : ArmState} {base : BitVec 64} {kind : Variant}
    {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (post : Delimited.Post (called s base kind) t limit data)
    (memory : u.mem = t.mem) :
    MemoryFrame (writesFor s kind (outcome s limit data).allocation) s u := by
  have resources := called_resources owned base
  have helperFrame := post.frame
  simp only [resources] at helperFrame
  have before := (local_covered s kind (outcome s limit data).allocation).frame (called_frame owned base)
  have after := (helper_writes owned base (outcome s limit data).allocation).frame helperFrame
  have frame := before.trans after
  intro address outside
  rw [memory]
  exact frame address outside

theorem post_of_helper {s t u : ArmState} {base : BitVec 64} {kind : Variant}
    {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (post : Delimited.Post (called s base kind) t limit data)
    (memory : u.mem = t.mem) (returned : Returned s u) : Post s u kind limit data := by
  have resources := called_resources owned base
  have allocation := (SszNative.Delimited.run_resources limit data (arenaOf s) owned.physical).1
  have frame := helper_post_frame owned post memory
  have physicalFrame : MemoryFrame (writesFor s kind (SszNative.Delimited.allocation data (arenaOf s))) s u := by
    simpa only [outcome, allocation] using frame
  have observes : widthLoad u = widthLoad t := by
    funext address bytes
    unfold widthLoad
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) bytes]
  have helperFrame := post.frame
  simp only [resources, allocation] at helperFrame
  have header : Protected (Delimited.writesFor (called s base kind)
      (SszNative.Delimited.allocation data (arenaOf s))) (helperOption s kind).toNat 24 := by
    have option := helper_option_owned owned base
    cases limit with
    | none => exact option
    | some cap => exact option.1
  have cap := called_words owned base
  have pointers : widthLoad u ((helperOption s kind).toNat + 8) 8 =
      widthLoad u ((optionAddress s kind).toNat + 8) 8 := by
    rw [observes, helperFrame.load _ 8 (by have := option_bound owned; omega)
      (by simpa only [called_option] using header.subspan 8 8 (by decide))]
    have original := physicalFrame.load ((optionAddress s kind).toNat + 8) 8
      (by have := original_option_bound owned; omega) ((original_option_owned owned).subspan 8 8 (by decide))
    rw [observes] at original
    rw [original]
    simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      congrArg (fun value : BitVec 64 => some value.toNat) cap.1
  have payloads : widthLoad u ((helperOption s kind).toNat + 16) 8 =
      widthLoad u ((optionAddress s kind).toNat + 16) 8 := by
    rw [observes, helperFrame.load _ 8 (by have := option_bound owned; omega)
      (by simpa only [called_option] using header.subspan 16 8 (by decide))]
    have original := physicalFrame.load ((optionAddress s kind).toNat + 16) 8
      (by have := original_option_bound owned; omega) ((original_option_owned owned).subspan 16 8 (by decide))
    rw [observes] at original
    rw [original]
    simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      congrArg (fun value : BitVec 64 => some value.toNat) cap.2
  have result : SszNative.Delimited.ResultAt (widthLoad u) (r (.GPR 0#5) s).toNat
      (r (.GPR 2#5) s).toNat (helperOption s kind).toNat data (outcome s limit data) := by
    simpa only [observes, called_out, called_source, called_option, resources, outcome] using post.result
  have arena := arena_readonly owned
  refine ⟨returned, result_relocate _ _ _ _ _ _ _ pointers payloads result, ?_, ?_, ?_, ?_, frame,
    physicalFrame.bytes _ _ owned.inputBound owned.inputOwned owned.input, ?_, ?_, ?_, ?_⟩
  · simpa only [observes, resources, outcome] using post.prepared
  · have readSame := (Memory.mem_eq_iff_read_mem_bytes_eq.mp memory) 8
      (r (.GPR 19#5) s + 16#64)
    simpa only [readSame, called_arena, resources, outcome] using post.cursor
  · exact physicalFrame.read _ 8 (by have := owned.arenaBound; omega)
      (by simpa using arena.subspan 0 8 (by decide))
  · have address : (r (.GPR 19#5) s + 8#64).toNat = (r (.GPR 19#5) s).toNat + 8 := by
      have bound := owned.arenaBound
      bv_omega
    exact physicalFrame.read _ 8 (by rw [address]; have := owned.arenaBound; omega)
      (by rw [address]; exact arena.subspan 8 8 (by decide))
  · intro address low high
    exact physicalFrame.protected_byte owned.inputOwned address low high
  · intro address low high
    exact physicalFrame.protected_byte owned.descriptorOwned address low high
  · intro capValue limitEq address
    dsimp only
    intro nonzero low high
    have countNonzero : read_mem_bytes 8 (optionAddress s kind + 16#64) s ≠ 0#64 := by
      intro zero
      simp only [zero, BitVec.toNat_ofNat] at high
      omega
    exact physicalFrame.protected_byte (owned.limbsOwned capValue limitEq nonzero countNonzero) address low high
  · intro kindEq
    subst kind
    exact activation_from_frame owned physicalFrame

end SszArm.BitList
