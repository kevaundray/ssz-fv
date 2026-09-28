import SszArm.BitVectorEntryExec
import SszArm.BitVectorCalls
import SszArm.BitVectorMemory

namespace SszArm.BitVector

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame)

/-- Physical state after the pre-call instructions and the actual first BL. -/
def divisionEntry (s : ArmState) (base : BitVec 64) : ArmState :=
  called .divide (Entry.result s base) base

structure DivisionArguments (s c : ArmState) (length : SszNative.NatOperand) : Prop where
  out : r (.GPR 0#5) c = r (.GPR 31#5) s + 144#64
  pointer : r (.GPR 1#5) c = length.pointer
  payload : r (.GPR 2#5) c = length.payload
  divisor : r (.GPR 3#5) c = 8#64
  arena : r (.GPR 4#5) c = r (.GPR 19#5) s
  sp : r (.GPR 31#5) c = r (.GPR 31#5) s
  memory : c.mem = s.mem
  observe : widthLoad c = widthLoad s
  resources : NatDivision.arenaOf c = arenaOf s

theorem division_arguments (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data) :
    DivisionArguments s (divisionEntry s base) length := by
  have pointer : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = length.pointer := by
    apply BitVec.eq_of_toNat_eq
    simpa only [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.ofNat_eq_ofNat,
      BitVec.setWidth_eq, Option.some.injEq] using owned.descriptor.1
  have payload : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = length.payload := by
    apply BitVec.eq_of_toNat_eq
    simpa only [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq, show 8#64 + 8#64 = 16#64 by decide,
      Option.some.injEq] using owned.descriptor.2.1
  constructor
  all_goals
    simp (config := {decide := true}) [divisionEntry, called, Entry.result, state_simp_rules, pointer, payload,
      widthLoad, NatDivision.arenaOf, arenaOf]
  funext address bytes
  simp only [UintCodec.widthLoad, state_simp_rules]

theorem division_outcome (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data) :
    NatDivision.outcome (divisionEntry s base) length = (outcome s length data).divided := by
  have args := division_arguments s base length data owned
  have divisor := args.divisor
  change r (.GPR 3#5) (divisionEntry s base) = (8 : BitVec 64) at divisor
  simp only [NatDivision.outcome, divisor, args.resources, outcome, divided_eq]

/-- Nested helper output and activation fit within the outer writable work area. -/
theorem division_locals (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data) :
    Covers (localWrites s) (NatDivision.localWrites (divisionEntry s base)) := by
  have args := division_arguments s base length data owned
  have low := owned.stackLow
  have high := owned.stackHigh
  have address : (r (.GPR 31#5) s + 144#64).toNat = (r (.GPR 31#5) s).toNat + 144 := by
    bv_omega
  intro span member
  simp only [NatDivision.localWrites, args.out, args.sp, address,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨((r (.GPR 31#5) s).toNat - 80, 352), by simp [localWrites], ?_, ?_⟩ <;> omega

theorem division_writes (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data) :
    Covers (writesFor s (outcome s length data))
      (NatDivision.writesFor (divisionEntry s base)
        (NatDivision.outcome (divisionEntry s base) length)) := by
  have args := division_arguments s base length data owned
  have divisor := args.divisor
  change r (.GPR 3#5) (divisionEntry s base) = (8 : BitVec 64) at divisor
  have locals := (local_covered s (outcome s length data)).trans
    (division_locals s base length data owned)
  have model : NatDivision.outcome (divisionEntry s base) length =
      SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used := by
    simp only [NatDivision.outcome, divisor, args.resources]
  cases allocated : (NatDivision.outcome (divisionEntry s base) length).allocation with
  | none => simpa only [NatDivision.writesFor, allocated] using locals
  | some reservation =>
    have member := divided_write s length data reservation (by simpa only [model] using allocated)
    have nonempty : (outcome s length data).writes ≠ [] := by
      intro empty
      simpa only [empty, List.not_mem_nil] using member
    intro span within
    simp only [NatDivision.writesFor, allocated, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, args.arena] at within
    rcases within with localMember | rfl | rfl
    · exact locals span localMember
    · exact cursor_covered s (outcome s length data) nonempty _ (by simp)
    · refine ⟨(reservation.pointer, 8 * (NatDivision.outcome (divisionEntry s base) length).written.length),
        ?_, Nat.le_refl _, Nat.le_refl _⟩
      have same : (reservation.pointer,
          8 * (NatDivision.outcome (divisionEntry s base) length).written.length) ∈
          (outcome s length data).writes := by simpa only [model] using member
      simp only [writesFor, List.mem_append]
      exact Or.inr same

/-- Every first-call ownership premise follows from physical body-entry memory
and separation, including the helper's nested eighty-byte call frame. -/
theorem division_owned (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes) (owned : Owned s length data) :
    NatDivision.Owned (divisionEntry s base) length := by
  have args := division_arguments s base length data owned
  have divisor := args.divisor
  change r (.GPR 3#5) (divisionEntry s base) = (8 : BitVec 64) at divisor
  have low := owned.stackLow
  have high := owned.stackHigh
  have output : (r (.GPR 0#5) (divisionEntry s base)).toNat =
      (r (.GPR 31#5) s).toNat + 144 := by rw [args.out]; bv_omega
  have locals := division_locals s base length data owned
  refine ⟨args.pointer, args.payload, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [args.observe]
    exact owned.descriptor.2.2
  · rw [args.divisor]
    decide
  · rw [output]
    omega
  · rw [args.sp]
    exact low
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    rw [args.sp, output]
    right
    omega
  · rw [args.arena]
    exact owned.arenaBound
  · rw [args.resources]
    exact owned.arenaStorage
  · rw [args.resources]
    exact owned.arenaNonnull
  · rw [args.arena]
    exact locals.protected owned.arenaLocal
  · intro reservation allocated
    have model : NatDivision.outcome (divisionEntry s base) length =
        SszNative.NatDivision.run length 8 (arenaOf s).base (arenaOf s).capacity (arenaOf s).used := by
      simp only [NatDivision.outcome, divisor, args.resources]
    have member := divided_write s length data reservation (by simpa only [model] using allocated)
    have fresh := owned.fresh _ member
    have cover : Covers (localWrites s ++
        [((r (.GPR 31#5) s).toNat + 272, 96), ((r (.GPR 19#5) s).toNat, 24)])
        (NatDivision.localWrites (divisionEntry s base) ++
          [((r (.GPR 4#5) (divisionEntry s base)).toNat, 24)]) := by
      intro span within
      simp only [List.mem_append, List.mem_singleton, args.arena] at within
      rcases within with localMember | rfl
      · obtain ⟨outer, outerMember, left, right⟩ := locals span localMember
        exact ⟨outer, List.mem_append_left _ outerMember, left, right⟩
      · exact ⟨((r (.GPR 19#5) s).toNat, 24), by simp, Nat.le_refl _, Nat.le_refl _⟩
    simpa only [model] using cover.protected fresh
  · exact (division_writes s base length data owned).operand length owned.operandOwned

/-- Actual physical entry, BL, arbitrary division scan/reservation, __udivti3,
and helper RET. Subsequent body stages start at the native return site 472. -/
theorem entry_divides (s : ArmState) (base : BitVec 64)
    (length : SszNative.NatOperand) (data : Ssz.Bytes)
    (owned : Owned s length data) (code : JointCodeAt s base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 428#64) :
    ∃ fuel t, run fuel s = t ∧ NatDivision.Post (divisionEntry s base) t length ∧
      JointCodeAt t base ∧ read_pc t = base + 472#64 := by
  have preparation := Entry.runs s base code.body error aligned pc
  have preparedCode : JointCodeAt (Entry.result s base) base := by
    rw [← preparation]
    exact code.run 10
  have preparedError : read_err (Entry.result s base) = .None := by
    simpa (config := {decide := true}) [Entry.result, state_simp_rules] using error
  have preparedAligned : CheckSPAlignment (Entry.result s base) := by
    simpa (config := {decide := true}) [Entry.result, CheckSPAlignment, state_simp_rules] using aligned
  have preparedPC : read_pc (Entry.result s base) = base + 468#64 := by
    simp only [Entry.result, state_simp_rules]
  obtain ⟨fuel, t, execution, post⟩ := divide_call (Entry.result s base) base length
    preparedCode preparedError preparedAligned preparedPC (division_owned s base length data owned)
  have whole : run (10 + fuel) s = t := by rw [run_plus, preparation, execution]
  refine ⟨10 + fuel, t, whole, post, ?_, ?_⟩
  · rw [← whole]
    exact code.run _
  · have returned := post.returned.pc
    simpa (config := {decide := true}) [divisionEntry, called, CallSite.offset, state_simp_rules] using returned

end SszArm.BitVector
