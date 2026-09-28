import SszArm.NatMulEntryFrame
import SszArm.NatMulRestore

namespace SszArm.NatMul

open Delimited (MemoryFrame Returned)

structure TailFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  output : r (.GPR 0#5) t = r (.GPR 0#5) s
  arena : r (.GPR 4#5) t = r (.GPR 5#5) s
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, 8 ≤ reg.toNat → reg.toNat ≤ 15 →
    (r (.SFP reg) t).setWidth 64 = (r (.SFP reg) s).setWidth 64
  memory : MemoryFrame (entryWrites s) s t

theorem restore_vectors (path : RestorePath) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (restored path s base) = r (.SFP reg) s := by
  refine NatMulStateFold.preserves (fun t (op : Op) => op.effect base t)
    (fun t => r (.SFP reg) t) path.ops s ?_
  intro op member t
  exact Op.sfp op base t reg

theorem EntryFrame.tail {s u : ArmState} (frame : EntryFrame s u) (base : BitVec 64) :
    TailFrame s (restored .tail u base) := by
  refine ⟨?_, ?_, (restore_argument_0 .tail u base).trans frame.output,
    (restore_tail_argument_4 u base).trans frame.arena,
    restore_stack .tail s u base frame.saved,
    restore_registers .tail s u base frame.saved, ?_, ?_⟩
  · simpa only [restored, block_program] using frame.program
  · simpa only [restored, block_error] using frame.error
  · intro reg low high
    rw [restore_vectors]
    exact frame.saved.vectors reg low high
  · intro address outside
    rw [restore_memory]
    exact frame.memory address outside

theorem TailFrame.returned {s u t : ArmState} (frame : TailFrame s u)
    (returned : Returned u t) : Returned s t := by
  refine ⟨returned.pc.trans (frame.registers 30#5 (by decide) (by decide)),
    returned.error, returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg low high
    exact (returned.registers reg low high).trans (frame.registers reg low high)
  · intro reg low high
    exact (returned.vectors reg low high).trans (frame.vectors reg low high)

theorem TailFrame.local_covered {s t : ArmState} (frame : TailFrame s t)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    BitVector.Covers (localWrites s result) (NatMulWord.localWrites t result) := by
  intro span member
  cases value : result.result with
  | ok output =>
    simp only [NatMulWord.localWrites, value, frame.sp, frame.output,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨((r (.GPR 31#5) s).toNat - 144, 144), by simp [localWrites, value], by omega, by omega⟩
    · exact ⟨((r (.GPR 0#5) s).toNat, 16), by simp [localWrites, value], le_rfl, le_rfl⟩
    · exact ⟨((r (.GPR 0#5) s).toNat + 64, 4), by simp [localWrites, value], le_rfl, le_rfl⟩
  | error error =>
    simp only [NatMulWord.localWrites, value, frame.sp, frame.output,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨((r (.GPR 31#5) s).toNat - 144, 144), by simp [localWrites, value], by omega, by omega⟩
    · exact ⟨((r (.GPR 0#5) s).toNat, 68), by simp [localWrites, value], le_rfl, le_rfl⟩

theorem covers_append_same {large small : List Delimited.Span}
    (cover : BitVector.Covers large small) (extra : List Delimited.Span) :
    BitVector.Covers (large ++ extra) (small ++ extra) := by
  intro span member
  rcases List.mem_append.mp member with before | after
  · obtain ⟨outer, member, low, high⟩ := cover span before
    exact ⟨outer, List.mem_append_left _ member, low, high⟩
  · exact ⟨span, List.mem_append_right _ after, le_rfl, le_rfl⟩

theorem TailFrame.writes_covered {s t : ArmState} (frame : TailFrame s t)
    (result : SszNative.NatArithmetic.Outcome SszNative.NatOperand) :
    BitVector.Covers (writesFor s result) (NatMulWord.writesFor t result) := by
  cases allocation : result.allocation with
  | none => simpa only [writesFor, NatMulWord.writesFor, allocation] using frame.local_covered result
  | some reservation =>
    simpa only [writesFor, NatMulWord.writesFor, allocation, frame.arena] using
      covers_append_same (frame.local_covered result)
        [((r (.GPR 5#5) s).toNat + 16, 8), (reservation.pointer, 8 * result.written.length)]

end SszArm.NatMul
