import SszArm.HashCombineDrain
import SszArm.HashCombineEntry
import SszArm.HashCombineReturn

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

def bodyWrites (s : ArmState) : List Span :=
  [stackSpan s 192, ((r (.GPR 31#5) s).toNat, 224)]

structure Activation (origin s : ArmState) : Prop where
  error : read_err s = .None
  program : s.program = origin.program
  aligned : CheckSPAlignment s
  sp : r (.GPR 31#5) s = bodySP origin
  output : r (.GPR 19#5) s = r (.GPR 0#5) origin
  statePointer : r (.GPR 24#5) s = r (.GPR 31#5) s
  saved : Saved origin s
  frame : MemoryFrame (combineWrites origin) origin s

structure LocalPost (s t : ArmState) : Prop where
  error : read_err t = .None
  program : t.program = s.program
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  output : r (.GPR 19#5) t = r (.GPR 19#5) s
  statePointer : r (.GPR 24#5) t = r (.GPR 24#5) s
  registers : ∀ reg : BitVec 5, 26 ≤ reg.toNat → reg.toNat ≤ 28 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  frame : MemoryFrame (bodyWrites s) s t

theorem Activation.physical {origin s : ArmState} (activation : Activation origin s)
    (low : 496 ≤ (r (.GPR 31#5) origin).toNat) :
    192 ≤ (r (.GPR 31#5) s).toNat ∧ (r (.GPR 31#5) s).toNat + 304 ≤ 2^64 := by
  rw [activation.sp]
  unfold bodySP
  constructor <;> bv_omega

theorem Activation.contained {origin s : ArmState} (activation : Activation origin s)
    (low : 496 ≤ (r (.GPR 31#5) origin).toNat) :
    ∀ span ∈ bodyWrites s, ∃ outer ∈ combineWrites origin,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  all_goals
    refine ⟨stackSpan origin 496, by simp [combineWrites], ?_, ?_⟩
    all_goals simp only [stackSpan, activation.sp, bodySP]; bv_omega

theorem Activation.after {origin s t : ArmState} (activation : Activation origin s)
    (low : 496 ≤ (r (.GPR 31#5) origin).toNat) (post : LocalPost s t) : Activation origin t := by
  have geometry := activation.physical low
  have savedProtected : Protected (bodyWrites s) (r (.GPR 31#5) s + 224#64).toNat 80 := by
    right
    intro span member
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals right; simp only [stackSpan]; bv_omega
  refine ⟨post.error, post.program.trans activation.program, ?_, post.sp.trans activation.sp,
    post.output.trans activation.output, ?_, ?_, ?_⟩
  · simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, post.sp] using activation.aligned
  · exact post.statePointer.trans (activation.statePointer.trans post.sp.symm)
  · exact activation.saved.of_frame post.frame geometry.2 savedProtected post.sp
      post.registers post.vectors
  · exact activation.frame.trans (frame_mono post.frame (activation.contained low))

theorem Activation.code {origin s : ArmState} {base : BitVec 64}
    (activation : Activation origin s) (code : CodeAt origin base) : CodeAt s base :=
  code.of_program_eq activation.program

theorem Activation.data {origin s : ArmState} {base : BitVec 64} {left right : ByteArray}
    (activation : Activation origin s) (owned : CombineOwned origin base left right)
    (data : DataAt origin base) : DataAt s base :=
  data.frame activation.frame owned.initialOwned owned.roundsOwned

theorem drain_contained_body (s : ArmState) :
    ∀ span ∈ drainWrites s, ∃ outer ∈ bodyWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  simp only [drainWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨stackSpan s 192, by simp [bodyWrites], ?_, ?_⟩ <;> simp only [stackSpan] <;> omega
  · exact ⟨((r (.GPR 31#5) s).toNat, 224), by simp [bodyWrites], by omega, by omega⟩

theorem DrainPost.local {side : Side} {s t : ArmState} {base : BitVec 64}
    (post : DrainPost side s t base) : LocalPost s t := by
  refine ⟨post.error, post.program, post.sp, ?_, ?_, ?_, post.vectors,
    frame_mono post.frame (drain_contained_body s)⟩
  · exact post.registers 19#5 (by decide) (by decide)
      (by cases side <;> decide) (by cases side <;> decide) (by decide)
  · exact post.registers 24#5 (by decide) (by decide)
      (by cases side <;> decide) (by cases side <;> decide) (by decide)
  · intro reg lo hi
    apply post.registers reg (by omega) (by omega)
    · cases side <;> simp only [Side.count] <;> bv_omega
    · cases side <;> simp only [Side.cursor] <;> bv_omega
    · bv_omega

theorem direct_contained_body (s : ArmState) (state : r (.GPR 24#5) s = r (.GPR 31#5) s)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    ∀ span ∈ directWrites s, ∃ outer ∈ bodyWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
  intro span member
  simp only [directWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨stackSpan s 192, by simp [bodyWrites], ?_, ?_⟩ <;> simp only [stackSpan] <;> omega
  · refine ⟨((r (.GPR 31#5) s).toNat, 224), by simp [bodyWrites], ?_, ?_⟩
    all_goals rw [state]; bv_omega

theorem Activation.directOwned {origin s : ArmState} {base address : BitVec 64}
    {left right input : ByteArray} {words : Vector UInt32 8}
    (activation : Activation origin s) (owned : CombineOwned origin base left right)
    (source : BytesAt origin address input) (physical : address.toNat + input.size ≤ 2^64)
    (inputProtected : Protected (combineWrites origin) address.toNat input.size)
    (chaining : ChainingAt s (r (.GPR 31#5) s + 64#64) words) :
    DirectOwned s base address input words := by
  have geometry := activation.physical owned.stackLow
  have inner := direct_contained_body s activation.statePointer (by omega)
  have outer := activation.contained owned.stackLow
  have included : ∀ span ∈ directWrites s, ∃ big ∈ combineWrites origin,
      big.1 ≤ span.1 ∧ span.1 + span.2 ≤ big.1 + big.2 := by
    intro span member
    obtain ⟨middle, inMiddle, lo, hi⟩ := inner span member
    obtain ⟨big, inBig, lower, upper⟩ := outer middle inMiddle
    exact ⟨big, inBig, by omega, by omega⟩
  refine ⟨physical, ?_, ?_, ?_, protected_writes_mono inputProtected included,
    protected_writes_mono owned.initialOwned included,
    protected_writes_mono owned.roundsOwned included,
    bytesAt_frame activation.frame physical inputProtected source, ?_⟩
  · rw [activation.statePointer]
    bv_omega
  · omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    right
    simp only [stackSpan, activation.statePointer]
    bv_omega
  · simpa only [activation.statePointer] using chaining

end SszArm.Hash.Combine
