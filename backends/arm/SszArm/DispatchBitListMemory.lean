import SszArm.DispatchBitListContract

namespace SszArm.DispatchBitList

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame NatOwned)
open Dispatch (bodySP entered)
open BitList (Variant optionAddress)
open BitVector (Covers)

theorem save_covered (s : ArmState) (kind : Variant) (allocation : Option SszNative.Arena.Reservation) :
    Covers (writesFor s kind allocation) [saveSpan s] := by
  intro span member
  simp only [List.mem_singleton] at member
  subst span
  exact ⟨saveSpan s, by simp [writesFor], Nat.le_refl _, Nat.le_refl _⟩

theorem body_covered (s : ArmState) (kind : Variant) (allocation : Option SszNative.Arena.Reservation) :
    Covers (writesFor s kind allocation) (bodyWrites s kind allocation) := by
  intro span member
  exact ⟨span, List.mem_cons_of_mem _ member, Nat.le_refl _, Nat.le_refl _⟩

theorem cons_covered (span : Span) (writes : List Span) : Covers (span :: writes) writes := by
  intro inner member
  exact ⟨inner, List.mem_cons_of_mem _ member, Nat.le_refl _, Nat.le_refl _⟩

theorem head_covered (span : Span) (writes : List Span) : Covers (span :: writes) [span] := by
  intro inner member
  simp only [List.mem_singleton] at member
  subst inner
  exact ⟨span, by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem entry_frame {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : MemoryFrame [saveSpan s] s (entered s (dispatchKind kind)) := by
  intro a outside
  have apart := outside (saveSpan s) (by simp)
  have low := owned.stackLow
  apply Dispatch.entered_frame s (dispatchKind kind) (by omega) a
  simp only [saveSpan] at apart
  omega

theorem Owned.entry {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : Dispatch.EntryOwned s (dispatchKind kind) := by
  have descriptor := (save_covered s kind _).protected owned.descriptorOwned
  have minimum : 8 ≤ kind.descriptorBytes := by cases kind <;> decide
  have bound := owned.descriptorBound
  have low := owned.stackLow
  refine ⟨by omega, by omega, ?_, owned.descriptor.tag⟩
  rcases descriptor with empty | separated
  · omega
  · have apart := separated (saveSpan s) (by simp)
    simp only [saveSpan] at apart
    omega

@[simp] theorem entered_option (s : ArmState) (kind : Variant) :
    optionAddress (entered s (dispatchKind kind)) kind = optionAddress s kind := by
  cases kind <;> simp (config := {decide := true}) [optionAddress]

@[simp] theorem entered_locals (s : ArmState) (kind : Variant) :
    BitList.localWrites (entered s (dispatchKind kind)) kind = localWrites s kind := by
  cases kind <;> simp (config := {decide := true})
    [BitList.localWrites, BitList.stackWrites, localWrites, stackWrites]

@[simp] theorem entered_writes (s : ArmState) (kind : Variant) (allocation : Option SszNative.Arena.Reservation) :
    BitList.writesFor (entered s (dispatchKind kind)) kind allocation = bodyWrites s kind allocation := by
  cases allocation <;> simp only [BitList.writesFor, bodyWrites, entered_locals, Dispatch.entered_arena]

theorem arena_read {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (offset bytes : Nat) (within : offset + bytes ≤ 24) :
    read_mem_bytes bytes (r (.GPR 4#5) s + BitVec.ofNat 64 offset) (entered s (dispatchKind kind)) =
      read_mem_bytes bytes (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
  by_cases empty : bytes = 0
  · subst bytes
    rfl
  have bound := owned.arenaBound
  have address : (r (.GPR 4#5) s + BitVec.ofNat 64 offset).toNat = (r (.GPR 4#5) s).toNat + offset := by
    bv_omega
  apply (entry_frame owned).read
  · rw [address]
    omega
  · rw [address]
    exact ((head_covered _ _).protected owned.arenaLocal).subspan offset bytes within

theorem entered_resources {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : BitList.arenaOf (entered s (dispatchKind kind)) = arenaOf s := by
  have base := arena_read owned 0 8 (by decide)
  have capacity := arena_read owned 8 8 (by decide)
  have cursor := arena_read owned 16 8 (by decide)
  simp only [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at base
  simp only [BitList.arenaOf, arenaOf, Dispatch.entered_arena, base, capacity, cursor]

theorem option_bound {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : (optionAddress s kind).toNat + 24 ≤ 2^64 := by
  have bound := owned.descriptorBound
  cases kind <;> simp only [optionAddress, Variant.descriptorBytes] at * <;> bv_omega

theorem option_owned {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : Protected [saveSpan s] (optionAddress s kind).toNat 24 := by
  have header := (save_covered s kind _).protected owned.descriptorOwned
  cases kind with
  | list => exact header
  | progressive =>
    have address : (optionAddress s .progressive).toNat = (r (.GPR 1#5) s).toNat + 8 := by
      have bound := owned.descriptorBound
      simp only [optionAddress, Variant.descriptorBytes] at *
      bv_omega
    rw [address]
    exact header.subspan 8 24 (by decide)

theorem option_read {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) (offset bytes : Nat) (within : offset + bytes ≤ 24) :
    read_mem_bytes bytes (optionAddress s kind + BitVec.ofNat 64 offset) (entered s (dispatchKind kind)) =
      read_mem_bytes bytes (optionAddress s kind + BitVec.ofNat 64 offset) s := by
  by_cases empty : bytes = 0
  · subst bytes
    rfl
  have bound := option_bound owned
  have address : (optionAddress s kind + BitVec.ofNat 64 offset).toNat = (optionAddress s kind).toNat + offset := by
    bv_omega
  apply (entry_frame owned).read
  · rw [address]
    omega
  · rw [address]
    exact (option_owned owned).subspan offset bytes within

theorem entered_descriptor {s : ArmState} {kind : Variant} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s kind limit data) : BitList.Descriptor (entered s (dispatchKind kind)) kind limit := by
  cases kind with
  | list =>
    cases limit with
    | none => exact False.elim owned.descriptor.payload
    | some cap =>
      have pointer := option_read owned 8 8 (by decide)
      have payload := option_read owned 16 8 (by decide)
      simp only [optionAddress] at pointer payload
      simp (config := {decide := true}) only [BitList.Descriptor, Dispatch.entered_reg,
        pointer, payload]
      exact (entry_frame owned).pair _ _ cap owned.descriptor.payload (by
        intro nonzero nonempty
        exact (save_covered s .list _).protected (owned.limbsOwned cap rfl nonzero nonempty))
  | progressive =>
    rw [BitList.Descriptor, entered_option]
    apply Delimited.option_preserved (entry_frame owned) _ limit (option_bound owned) owned.descriptor.payload
    cases limit with
    | none => exact option_owned owned
    | some cap =>
      refine ⟨option_owned owned, ?_⟩
      intro nonzero nonempty
      exact (save_covered s .progressive _).protected (owned.limbsOwned cap rfl nonzero nonempty)

end SszArm.DispatchBitList
