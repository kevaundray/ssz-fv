import SszArm.BitVectorLeafOwned
import SszArm.BitVectorRoundModel

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Protected)

structure RoundArguments (s c : ArmState) (length quotient : SszNative.NatOperand) : Prop where
  output : r (.GPR 0#5) c = r (.GPR 31#5) s + 144#64
  leftPointer : r (.GPR 1#5) c = quotient.pointer
  leftPayload : r (.GPR 2#5) c = quotient.payload
  rightPointer : r (.GPR 3#5) c = (SszNative.NatOperand.small 1).pointer
  rightPayload : r (.GPR 4#5) c = (SszNative.NatOperand.small 1).payload
  arena : r (.GPR 5#5) c = r (.GPR 19#5) s
  sp : r (.GPR 31#5) c = r (.GPR 31#5) s
  leftAt : quotient.At (widthLoad c)
  resources : NatAdd.arenaOf c =
    ⟨(arenaOf s).base, (arenaOf s).capacity,
      (SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used).used⟩

theorem RoundArguments.model {s c : ArmState} {length quotient : SszNative.NatOperand}
    (args : RoundArguments s c length quotient) :
    NatAdd.outcome c quotient (.small 1) = rounding s length quotient := by
  simp only [NatAdd.outcome, args.resources, rounding]

theorem round_locals {s c : ArmState} {length quotient : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (args : RoundArguments s c length quotient) :
    Covers (localWrites s) (NatAdd.localWrites c) :=
  leaf_locals_covered owned 68 (by decide) args.output args.sp

theorem round_envelope {s c : ArmState} {length quotient : SszNative.NatOperand} {data : Ssz.Bytes}
    (owned : Owned s length data) (args : RoundArguments s c length quotient) :
    Covers (localWrites s ++
        [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
      (NatAdd.localWrites c ++ [((r (.GPR 5#5) c).toNat, 24)]) := by
  intro span member
  simp only [List.mem_append, List.mem_singleton, args.arena] at member
  rcases member with inLocals | rfl
  · obtain ⟨outer, within, low, high⟩ := round_locals owned args span inLocals
    exact ⟨outer, List.mem_append_left _ within, low, high⟩
  · exact ⟨((r (.GPR 19#5) s).toNat, 24), by simp, Nat.le_refl _, Nat.le_refl _⟩

theorem round_writes {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (args : RoundArguments s c length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) :
    Covers (writesFor s (outcome s length data)) (NatAdd.writesFor c (NatAdd.outcome c quotient (.small 1))) := by
  have locals := (local_covered s (outcome s length data)).trans (round_locals owned args)
  cases allocated : (NatAdd.outcome c quotient (.small 1)).allocation with
  | none => simpa only [NatAdd.writesFor, allocated] using locals
  | some reservation =>
    have member := rounded_write s length quotient remainder data division nonzero reservation
      (by simpa only [args.model] using allocated)
    have nonempty : (outcome s length data).writes ≠ [] := by
      intro empty
      simpa only [empty, List.not_mem_nil] using member
    intro span within
    simp only [NatAdd.writesFor, allocated, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, args.arena] at within
    rcases within with inLocals | rfl | rfl
    · exact locals span inLocals
    · exact cursor_covered s (outcome s length data) nonempty _ (by simp)
    · refine ⟨(reservation.pointer, 8 * (NatAdd.outcome c quotient (.small 1)).written.length),
        ?_, Nat.le_refl _, Nat.le_refl _⟩
      have same : (reservation.pointer, 8 * (NatAdd.outcome c quotient (.small 1)).written.length) ∈
          (outcome s length data).writes := by simpa only [args.model] using member
      simp only [writesFor, List.mem_append]
      exact Or.inr same

/-- Even if rounding reserves a new buffer and then a later stage fails, its
writes do not damage the first helper's physical quotient buffer. -/
theorem round_quotient_owned {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (args : RoundArguments s c length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder)) :
    NatAdd.OperandOwned (NatAdd.writesFor c (NatAdd.outcome c quotient (.small 1))) quotient := by
  rcases quotient_origin length quotient remainder (arenaOf s).base (arenaOf s).capacity
    (arenaOf s).used division with ⟨value, rfl⟩ | ⟨first, allocated, rfl⟩
  · trivial
  · have fresh := owned.fresh _ (divided_write s length data first allocated)
    have common := (round_envelope owned args).protected fresh
    have extent := division_allocation_end length (arenaOf s) first allocated
    have cursor := (division_cursor_bounds s length data owned).2
    rw [outcome, divided_eq] at cursor
    have size := (SszNative.NatDivision.allocation_resources length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used first allocated).2.1
    have positive : 0 < (SszNative.NatDivision.run length 8 (arenaOf s).base
        (arenaOf s).capacity (arenaOf s).used).written.length := by
      split at size <;> omega
    have storage := owned.arenaStorage
    have pointerBound : first.pointer < 2^64 := by omega
    apply NatAdd.LargeCorrect.fromWords_owned
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound]
    cases second : (NatAdd.outcome c
        (SszNative.NatOperand.fromWords (BitVec.ofNat 64 first.pointer)
          (SszNative.NatDivision.run length 8 (arenaOf s).base
            (arenaOf s).capacity (arenaOf s).used).written) (.small 1)).allocation with
    | none =>
      simp only [NatAdd.writesFor, second]
      exact (show Covers (NatAdd.localWrites c ++ [((r (.GPR 5#5) c).toNat, 24)])
          (NatAdd.localWrites c) from fun span member =>
            ⟨span, List.mem_append_left _ member, Nat.le_refl _, Nat.le_refl _⟩).protected common
    | some reservation =>
      have ordered := allocations_ordered length _ (arenaOf s) first reservation allocated
        (by simpa only [args.model, rounding] using second)
      simp only [NatAdd.writesFor, second]
      rcases common with empty | separate
      · exact Or.inl empty
      · right
        intro span member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with inLocals | rfl | rfl
        · exact separate span (List.mem_append_left _ inLocals)
        · have header := separate ((r (.GPR 5#5) c).toNat, 24) (by simp)
          omega
        · exact Or.inl ordered

theorem round_owned {s c : ArmState} {length quotient : SszNative.NatOperand}
    {data : Ssz.Bytes} {remainder : BitVec 64} (owned : Owned s length data)
    (args : RoundArguments s c length quotient)
    (division : (SszNative.NatDivision.run length 8 (arenaOf s).base
      (arenaOf s).capacity (arenaOf s).used).result = .ok (quotient, remainder))
    (nonzero : remainder ≠ 0) : NatAdd.Owned c quotient (.small 1) := by
  have low := owned.stackLow
  have high := owned.stackHigh
  have outNat : (r (.GPR 0#5) c).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    rw [args.output]
    bv_omega
  refine ⟨args.leftPointer, args.leftPayload, args.rightPointer, args.rightPayload,
    args.leftAt, by trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by trivial⟩
  · rw [outNat]; omega
  · rw [args.sp]; omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    simp only [outNat, args.sp]
    omega
  · rw [args.arena]; exact owned.arenaBound
  · rw [args.resources]; exact owned.arenaStorage
  · rw [args.resources]; exact owned.arenaNonnull
  · rw [args.arena]; exact (round_locals owned args).protected owned.arenaLocal
  · intro reservation allocated
    have member := rounded_write s length quotient remainder data division nonzero reservation
      (by simpa only [args.model] using allocated)
    simpa only [args.model] using (round_envelope owned args).protected (owned.fresh _ member)
  · exact round_quotient_owned owned args division

end SszArm.BitVector
