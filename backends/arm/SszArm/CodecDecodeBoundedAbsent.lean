import SszArm.CodecDecodeBoundedActivation
import SszArm.CodecDecodeBoundedEntry
import SszArm.CodecDecodeBoundedReturn
import SszArm.CodecDecodeBoundedPreservation

namespace SszArm.Codec.Decode.Bounded

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

@[irreducible] def absentState (s : ArmState) (base : BitVec 64) : ArmState :=
  restored (Emit.statusStored (tagRead (prologue s base) base))

theorem absent_tag (s : ArmState) (base : BitVec 64) (actual : SszNative.NatOperand)
    (owned : Owned s none actual) :
    read_mem_bytes 4 (r (.GPR 1#5) (prologue s base)) (prologue s base) = 0#32 := by
  rw [prologue_register s base 1#5 (by decide)]
  have frame : MemoryFrame (localWrites s) s (prologue s base) :=
    (prologue_frame s base owned.stackBound).weaken (by
      intro span member; simp only [localWrites, List.mem_cons]; exact Or.inr member)
  exact (inputs_preserved owned frame).1

/-- The absent Option reads no payload and executes the actual status-store and
restoring RET. No comparison call or allocation occurs. -/
theorem absent_run (s : ArmState) (base : BitVec 64) (actual : SszNative.NatOperand)
    (owned : Owned s none actual) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base) :
    run 22 s = absentState s base := by
  let p := prologue s base
  let q := tagRead p base
  have pRun : run 4 s = p := prologue_run s base code error aligned pc
  have pCode : CodeAt p base := by
    simpa only [p, CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt, prologue_program] using code
  have pError : read_err p = .None := by simpa [p] using error
  have pAligned : CheckSPAlignment p := prologue_aligned s base aligned
  have pPC : read_pc p = base + 16#64 := by simp [p, pc]
  have qRun : run 4 p = q := tag_run p base pCode pError pAligned pPC
  have qCode : CodeAt q base := by
    simpa only [q, tagRead, CodeAt, Linked.Bounded.CodeAt, Linked.WordsAt,
      state_simp_rules] using pCode
  have qError : read_err q = .None := by simpa [q, tagRead, state_simp_rules] using pError
  have qAligned : CheckSPAlignment q := by
    simpa [q, tagRead, CheckSPAlignment, state_simp_rules] using pAligned
  have qPC : read_pc q = base + 196#64 := by
    have tag := absent_tag s base actual owned
    simp [q, p, tagRead, state_simp_rules, tag]
  have finish := success_run q base qCode qError qAligned qPC
  rw [show 22 = 4 + 4 + 14 by decide, run_plus, run_plus, pRun, qRun, finish]
  rfl

def absentMemory (s : ArmState) : ArmState :=
  write_mem_bytes 4 (r (.GPR 0#5) s + 64#64) 0#32
    (write_mem_bytes 8 (r (.GPR 31#5) s - 56#64) (r (.GPR 10#5) s)
      (write_mem_bytes 8 (r (.GPR 31#5) s - 64#64) (r (.GPR 9#5) s) (savedMemory s)))

@[simp] theorem absent_memory (s : ArmState) (base : BitVec 64) :
    (absentState s base).mem = (absentMemory s).mem := by
  simp only [absentState, restored_memory, Emit.statusStored_memory, Emit.statusMemory]
  simp [tagRead, state_simp_rules, prologue_sp, prologue_register, bodySP,
    BitVec.sub_eq_add_neg, BitVec.add_assoc, absentMemory]
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes, ArmState.mem_w_eq_mem,
    prologue_memory]

theorem absent_frame (s : ArmState) (base : BitVec 64) (actual : SszNative.NatOperand)
    (owned : Owned s none actual) :
    MemoryFrame (writesFor s (.ok ())) s (absentState s base) := by
  have low := owned.stackBound
  have high := owned.resultBound
  intro address outside
  have status := outside ((r (.GPR 0#5) s).toNat + 64, 4) (by simp [writesFor])
  have scratch := outside ((r (.GPR 31#5) s).toNat - 64, 16) (by simp [writesFor, stackWrites])
  have link := outside ((r (.GPR 31#5) s).toNat - 48, 8) (by simp [writesFor, stackWrites])
  have saved := outside ((r (.GPR 31#5) s).toNat - 32, 32) (by simp [writesFor, stackWrites])
  simp only [Prod.fst, Prod.snd] at status scratch link saved
  rw [absent_memory]
  simp (disch := bv_omega) only [absentMemory, savedMemory, bodySP,
    BoolCodec.write_mem_bytes_frame]

theorem absent_status (s : ArmState) (base : BitVec 64)
    (bound : (r (.GPR 0#5) s).toNat + 68 ≤ 2 ^ 64) :
    ResultAt (absentState s base) (r (.GPR 0#5) s).toNat (.ok ()) := by
  change some (read_mem_bytes 4 (BitVec.ofNat 64 ((r (.GPR 0#5) s).toNat + 64))
    (absentState s base)).toNat = some 0
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp (absent_memory s base)]
  simp only [absentMemory, BitVec.ofNat_add, BitVec.ofNat_toNat]
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_same _ 4 _ _ (by bv_omega)]
  rfl

end SszArm.Codec.Decode.Bounded
