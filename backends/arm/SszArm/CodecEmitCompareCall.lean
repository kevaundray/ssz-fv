import SszArm.CodecLinkedPreserve
import SszArm.CodecLinkedBranches
import SszArm.NatCompareProofs
import SszArm.CodecStack

namespace SszArm.Codec.Emit.Union

open UintCodec (widthLoad)

/-- The concrete state after the BL at emit+1652, before Nat.compare starts. -/
def compareEntry (s : ArmState) (bias : BitVec 64) : ArmState :=
  w (.GPR 30#5) (bias + 2296436#64) (w .PC (bias + 2250156#64) s)

structure Compared (s t : ArmState) (bias : BitVec 64) (left right : Nat) : Prop where
  pc : read_pc t = bias + 2296436#64
  error : read_err t = .None
  program : t.program = s.program
  stack : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  frame : Delimited.MemoryFrame (Stack.envelope (r (.GPR 31#5) s).toNat 16) s t
  ordering : (r (.GPR 0#5) t).setWidth 8 = SszNative.NatABI.orderingByte (compare left right)

/-- Invoke the immutable proof at the actual linked helper address. Its run is
constructed here; no callee execution is part of the precondition. -/
theorem compare_call (s : ArmState) (bias : BitVec 64) (left right : Nat)
    (code : Linked.CodeAt s bias) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = bias + 2296432#64)
    (lhs : SszNative.NatMemory.Pair (widthLoad s) (r (.GPR 0#5) s) (r (.GPR 1#5) s) left)
    (rhs : SszNative.NatMemory.Pair (widthLoad s) (r (.GPR 2#5) s) (r (.GPR 3#5) s) right)
    (leftOwned : NatCompare.Owned s (r (.GPR 0#5) s) (r (.GPR 1#5) s))
    (rightOwned : NatCompare.Owned s (r (.GPR 2#5) s) (r (.GPR 3#5) s)) :
    ∃ fuel t, run fuel s = t ∧ Compared s t bias left right := by
  have fetched := Linked.Emit.chunk6_codeAt code.emit (1652, 0x97ffd2cf#32) (by decide)
  have fetched' : s.program.find? (bias + 2296432#64) = some 0x97ffd2cf#32 := by
    simpa only [BitVec.add_assoc, BitVec.ofNat_add_ofNat] using fetched
  have call : stepi s = compareEntry s bias :=
    Linked.Branches.emit_p1652 s bias error pc fetched'
  have codeAt : NatCompare.CodeAt (compareEntry s bias) (bias + 2250156#64) := by
    simpa only [NatCompare.CodeAt, compareEntry, state_simp_rules] using code.compare
  have entryError : read_err (compareEntry s bias) = .None := by
    simpa (config := {decide := true, instances := true}) [compareEntry, state_simp_rules] using error
  have entryAligned : CheckSPAlignment (compareEntry s bias) := by
    simpa (config := {decide := true, instances := true})
      [CheckSPAlignment, compareEntry, state_simp_rules] using aligned
  have entryPC : read_pc (compareEntry s bias) = bias + 2250156#64 + BitVec.ofNat 64 NatCompare.entry := by
    simp [compareEntry, NatCompare.entry, state_simp_rules]
  have entryLoad : widthLoad (compareEntry s bias) = widthLoad s := by
    funext address bytes
    unfold widthLoad
    simp [compareEntry, state_simp_rules]
  have entryLhs : SszNative.NatMemory.Pair (widthLoad (compareEntry s bias))
      (r (.GPR 0#5) (compareEntry s bias)) (r (.GPR 1#5) (compareEntry s bias)) left := by
    rw [entryLoad]
    simpa (config := {decide := true, instances := true})
      [compareEntry, state_simp_rules] using lhs
  have entryRhs : SszNative.NatMemory.Pair (widthLoad (compareEntry s bias))
      (r (.GPR 2#5) (compareEntry s bias)) (r (.GPR 3#5) (compareEntry s bias)) right := by
    rw [entryLoad]
    simpa (config := {decide := true, instances := true})
      [compareEntry, state_simp_rules] using rhs
  have entryLeftOwned : NatCompare.Owned (compareEntry s bias)
      (r (.GPR 0#5) (compareEntry s bias)) (r (.GPR 1#5) (compareEntry s bias)) := by
    simpa (config := {decide := true, instances := true})
      [NatCompare.Owned, compareEntry, state_simp_rules] using leftOwned
  have entryRightOwned : NatCompare.Owned (compareEntry s bias)
      (r (.GPR 2#5) (compareEntry s bias)) (r (.GPR 3#5) (compareEntry s bias)) := by
    simpa (config := {decide := true, instances := true})
      [NatCompare.Owned, compareEntry, state_simp_rules] using rightOwned
  obtain ⟨fuel, t, execution, frame, returned, finalError, stack, _, ordering, _, _⟩ :=
    NatCompare.compare_correct (compareEntry s bias) (bias + 2250156#64) left right
      codeAt entryError entryAligned entryPC entryLhs entryRhs entryLeftOwned entryRightOwned
  refine ⟨fuel + 1, t, ?_, ?_⟩
  · rw [run, call]
    exact execution
  · refine ⟨?_, finalError, ?_, ?_, ?_, ?_, ?_, ordering⟩
    · simpa only [compareEntry, state_simp_rules] using returned
    · simpa only [compareEntry, state_simp_rules] using frame.program
    · simpa (config := {decide := true, instances := true}) [compareEntry, state_simp_rules] using stack
    · intro reg untouched
      have notLR : reg ≠ 30#5 := by
        intro same
        exact untouched (by simp [same])
      have helperUntouched : reg ∉ [0#5, 8#5, 9#5, 10#5, 11#5, 12#5] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched ⊢
        exact ⟨untouched.1, untouched.2.1, untouched.2.2.1, untouched.2.2.2.1,
          untouched.2.2.2.2.1, untouched.2.2.2.2.2.1⟩
      simpa (config := {decide := true, instances := true})
        [compareEntry, state_simp_rules, notLR] using frame.registers reg helperUntouched
    · intro reg
      simpa (config := {decide := true, instances := true})
        [compareEntry, state_simp_rules] using frame.vectors reg
    · intro address outside
      have apart := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [Stack.envelope])
      have low := leftOwned.1
      have safe : address.toNat < (r (.GPR 31#5) (compareEntry s bias)).toNat - 16 ∨
          (r (.GPR 31#5) (compareEntry s bias)).toNat ≤ address.toNat := by
        simp (config := {decide := true, instances := true}) only [compareEntry, state_simp_rules]
        simp only [Prod.fst, Prod.snd] at apart
        omega
      simpa only [compareEntry, state_simp_rules] using frame.memory address safe

end SszArm.Codec.Emit.Union
