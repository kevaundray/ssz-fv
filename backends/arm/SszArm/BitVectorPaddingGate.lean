import SszArm.BitVectorPaddingGateModel

namespace SszArm.BitVector.PaddingGate

open Delimited (MemoryFrame)
open UintCodec (widthLoad)

@[simp] theorem gate_program (c : ArmState) (base : BitVec 64) :
    (TailGate.result c base).program = c.program := by
  simp [TailGate.result, state_simp_rules]

theorem gate_counted {s c : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (base : BitVec 64) :
    Counted s (TailGate.result c base) length remainder := by
  apply counted_of_preserved current
  · simp [TailGate.result, state_simp_rules]
  · intro reg h8 h9; simp [TailGate.result, state_simp_rules]
  · intro reg; simp [TailGate.result, state_simp_rules]

theorem gate_aligned (c : ArmState) (base : BitVec 64) (aligned : CheckSPAlignment c) :
    CheckSPAlignment (TailGate.result c base) := by
  simpa (config := {decide := true, instances := true})
    [TailGate.result, CheckSPAlignment, state_simp_rules] using aligned

theorem gate_frame (s c : ArmState) (base : BitVec 64) :
    MemoryFrame (localWrites s) c (TailGate.result c base) := by
  intro address outside
  simp [TailGate.result, ArmState.mem_w_eq_mem]

theorem gate_pc {s c : ArmState} {length : SszNative.NatOperand} {data : Ssz.Bytes}
    {remainder : BitVec 64} (owned : Owned s length data)
    (current : Counted s c length remainder) (base : BitVec 64) :
    read_pc (TailGate.result c base) =
      if data.size = 0 then base + 6576#64
      else if remainder = 0#64 then base + 6576#64 else base + 6008#64 := by
  have size : (r (.GPR 20#5) c).toNat = data.size := by
    rw [current.size]; exact owned.length
  have empty : r (.GPR 20#5) c = 0#64 ↔ data.size = 0 := by
    rw [← BitVec.toNat_inj]
    simp only [size, BitVec.toNat_ofNat]
  simp only [TailGate.result, state_simp_rules, empty, current.remainderValue]

theorem checked_aligned (c : ArmState) (base : BitVec 64) (aligned : CheckSPAlignment c) :
    CheckSPAlignment (checked c base) := by
  simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq,
    checked_register c base 31#5 (by decide) (by decide)] using aligned

theorem completed_counted {s c : ArmState} {length : SszNative.NatOperand} {remainder : BitVec 64}
    (current : Counted s c length remainder) (base : BitVec 64) :
    Counted s (Padding.completed c base) length remainder :=
  counted_of_preserved current (Padding.completed_error c base)
    (Padding.completed_register c base) (Padding.completed_vector c base)

/-- The condition matches the shared finish function after exact scope succeeds. -/
theorem finish_eq (length expected : SszNative.NatOperand) (remainder : BitVec 64) (data : Ssz.Bytes)
    (scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true) :
    SszNative.BitVector.finish length expected remainder data =
      if Bad remainder data then .error .paddingBits else SszNative.BitVector.construct length data := by
  by_cases rem : remainder = 0#64
  · simp [SszNative.BitVector.finish, scope, Bad, rem]
  · by_cases nonempty : 0 < data.size
    · by_cases zero : data[data.size - 1]! >>> UInt8.ofNat remainder.toNat = 0 <;>
        simp [SszNative.BitVector.finish, scope, Bad, rem, nonempty, zero]
    · simp [SszNative.BitVector.finish, scope, Bad, rem, nonempty]

structure Post (s c t : ArmState) (base : BitVec 64) (length : SszNative.NatOperand)
    (remainder : BitVec 64) (data : Ssz.Bytes) : Prop where
  counted : Counted s t length remainder
  program : t.program = c.program
  frame : MemoryFrame (localWrites s) c t
  bytes : SszNative.ByteView.BytesAt (widthLoad t) (r (.GPR 2#5) s).toNat data
  branch : if Bad remainder data then
    read_pc t = base + 4732#64 ∧
      SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (r (.GPR 2#5) s).toNat data (.error .paddingBits)
    else read_pc t = base + 6576#64

private theorem post_of_fields {s c t : ArmState} {base : BitVec 64}
    {length : SszNative.NatOperand} {remainder : BitVec 64} {data : Ssz.Bytes}
    (owned : Owned s length data)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data)
    (current : Counted s t length remainder) (program : t.program = c.program)
    (frame : MemoryFrame (localWrites s) c t)
    (branch : if Bad remainder data then
      read_pc t = base + 4732#64 ∧
        SszNative.BitVector.ResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
          (r (.GPR 2#5) s).toNat data (.error .paddingBits)
      else read_pc t = base + 6576#64) : Post s c t base length remainder data :=
  ⟨current, program, frame, bytes_after_frame owned frame bytes, branch⟩

/-- Empty input and zero remainder branch before any last-byte load. Otherwise
all reads, the logical shift, and either the shared error tail or continuation
are obtained from the actual linked instructions. -/
theorem decision {s c : ArmState} {length expected : SszNative.NatOperand}
    {remainder : BitVec 64} {data : Ssz.Bytes} (base : BitVec 64)
    (owned : Owned s length data) (current : Counted s c length remainder)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (BitVec.ofNat 64 data.size) = true)
    (code : CodeAt c base) (pc : read_pc c = base + 6000#64) (aligned : CheckSPAlignment c)
    (bytes : SszNative.ByteView.BytesAt (widthLoad c) (r (.GPR 2#5) s).toNat data) :
    ∃ fuel t, run fuel c = t ∧ Post s c t base length remainder data ∧
      SszNative.BitVector.finish length expected remainder data =
        if Bad remainder data then .error .paddingBits else SszNative.BitVector.construct length data := by
  have semantic := finish_eq length expected remainder data scope
  have gateRun := TailGate.executes c base code current.error pc
  have gateCurrent := gate_counted current base
  have gateFrame := gate_frame s c base
  have gateBytes := bytes_after_frame owned gateFrame bytes
  have gateCode : CodeAt (TailGate.result c base) base := by
    simpa only [CodeAt, gate_program] using code
  have gateAligned := gate_aligned c base aligned
  have gatePC := gate_pc owned current base
  by_cases empty : data.size = 0
  · refine ⟨(TailGate.ops c).length, TailGate.result c base, gateRun, ?_, semantic⟩
    apply post_of_fields owned bytes gateCurrent (gate_program c base) gateFrame
    simpa [Bad, empty] using gatePC
  · by_cases divisible : remainder = 0#64
    · refine ⟨(TailGate.ops c).length, TailGate.result c base, gateRun, ?_, semantic⟩
      apply post_of_fields owned bytes gateCurrent (gate_program c base) gateFrame
      simpa [Bad, empty, divisible] using gatePC
    · have nonempty : 0 < data.size := by omega
      have start : read_pc (TailGate.result c base) = base + 6008#64 := by
        simpa only [empty, divisible, ↓reduceIte] using gatePC
      have checkRun := checked_run _ base gateCode gateCurrent.error gateAligned start
      have checkCurrent := checked_counted gateCurrent base
      have checkFrame := checked_frame owned gateCurrent base
      have totalFrame := gateFrame.trans checkFrame
      have checkProgram : (checked (TailGate.result c base) base).program = c.program :=
        (checked_program _ _).trans (gate_program c base)
      have checkPC := checked_pc owned gateCurrent base nonempty gateBytes arithmetic
      by_cases zero : data[data.size - 1]! >>> UInt8.ofNat remainder.toNat = 0
      · refine ⟨(TailGate.ops c).length + 11, checked (TailGate.result c base) base,
          ?_, ?_, semantic⟩
        · rw [run_plus, gateRun, checkRun]
        · apply post_of_fields owned bytes checkCurrent checkProgram totalFrame
          simpa [Bad, zero] using checkPC
      · have paddingPC : read_pc (checked (TailGate.result c base) base) = base + 6052#64 := by
          simpa only [zero, ↓reduceIte] using checkPC
        have paddingRun := Padding.completed_run _ base (padding_space owned checkCurrent)
          (by simpa only [CodeAt, checked_program] using gateCode) checkCurrent.error
          (checked_aligned _ _ gateAligned) paddingPC
        have paddingFrame := (padding_cover owned checkCurrent).frame
          (Padding.completed_frame _ base (padding_space owned checkCurrent))
        refine ⟨(TailGate.ops c).length + (11 + 52),
          Padding.completed (checked (TailGate.result c base) base) base, ?_, ?_, semantic⟩
        · rw [run_plus, gateRun, run_plus, checkRun, paddingRun]
        · apply post_of_fields owned bytes (completed_counted checkCurrent base)
            ((Padding.completed_program _ _).trans checkProgram) (totalFrame.trans paddingFrame)
          have bad : Bad remainder data := ⟨divisible, nonempty, zero⟩
          rw [if_pos bad]
          refine ⟨Padding.completed_pc _ _, ?_⟩
          simpa only [checkCurrent.output] using
            Padding.completed_result _ base (padding_space owned checkCurrent)
              (r (.GPR 2#5) s).toNat data

end SszArm.BitVector.PaddingGate
