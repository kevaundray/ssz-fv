import SszArm.DelimitedContract
import SszArm.DelimitedPrologue
import SszArm.DelimitedInput
import SszArm.DelimitedEmpty

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem Owned.empty_owned {s : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) (empty : r (.GPR 3#5) s = 0#64) : EmptyOwned s := by
  have stack := owned.stackBound
  simp only [activationSpan, empty, ↓reduceIte] at stack
  have separate : (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat := by
    rcases owned.outputStack with impossible | apart
    · omega
    · have separated := apart (activationSpan s) (by simp)
      simp only [activationSpan, empty, ↓reduceIte] at separated
      omega
  exact ⟨stack, owned.outputBound, separate⟩

/-- Empty input reaches the actual early RET and the complete shared-model post. -/
theorem empty_model_correct (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry) (empty : data.size = 0) :
    ∃ t, run 19 s = t ∧ Post s t limit data := by
  have zero : r (.GPR 3#5) s = 0#64 := by
    have length := owned.length
    bv_omega
  obtain ⟨t, executed, returned, frame, result⟩ :=
    empty_correct s base hc he ha hp zero (owned.empty_owned zero)
  refine ⟨t, executed, post_of_frame s t limit data owned returned ?_ ?_ ?_ ?_⟩
  · simpa [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
      SszNative.Delimited.ResultAt] using result
  · simp [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
      SszNative.Delimited.Outcome.PreparedAt]
  · have original := frame.load ((r (.GPR 4#5) s).toNat + 16) 8 (by
        have bound := owned.arenaBound
        omega) (owned.arenaLocal.subspan 16 8 (by decide))
    have words := Option.some.inj original
    simpa [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
      arenaOf, widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using words
  · simpa [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
      SszNative.Delimited.Outcome.allocation, writesFor] using frame

/-- A nonempty entry checkpoint contains only observations needed by the next
blocks, rather than the unfolded saved-register/memory state. -/
structure Started (s t : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) : Prop where
  program : t.program = s.program
  error : read_err t = .None
  aligned : CheckSPAlignment t
  saved : Saved s t
  arguments : ∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] →
    r (.GPR reg) t = r (.GPR reg) s
  preceding : r (.GPR 25#5) t = r (.GPR 3#5) s - 1#64
  byte : r (.GPR 8#5) t = data[data.size - 1]!.toBitVec.setWidth 64
  pc : read_pc t = if data[data.size - 1]! = 0 then base + 184#64 else base + 64#64
  frame : MemoryFrame (localWrites s) s t
  inputs : InputsPreserved s t limit data

/-- Entry CBZ, six real save pairs, and the last-byte load are all included. -/
theorem nonempty_start (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry) (nonempty : 0 < data.size) :
    ∃ t, run 16 s = t ∧ Started s t base limit data := by
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
    have length := owned.length
    bv_omega
  have stack : 112 ≤ (r (.GPR 31#5) s).toNat := by
    simpa only [activationSpan, nonzero, ↓reduceIte] using owned.stackBound
  let u := Op.p0.effect base s
  let t := block base prologueOps u
  have stackU : 112 ≤ (r (.GPR 31#5) u).toNat := by
    simpa [u, Op.effect, state_simp_rules] using stack
  have nonzeroU : r (.GPR 3#5) u ≠ 0#64 := by
    simpa [u, Op.effect, state_simp_rules] using nonzero
  have frame : MemoryFrame (localWrites s) s t := by
    have savedFrame := prologue_frame u base stackU nonzeroU
    simpa [t, MemoryFrame, localWrites, activationSpan, u, Op.effect,
      state_simp_rules] using savedFrame
  have inputs : InputsPreserved s t limit data :=
    inputs_preserved owned (local_frame (SszNative.Delimited.allocation data (arenaOf s)) frame)
  have savedU := prologue_saved u base stackU
  have saved : Saved s t := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [t, u, Op.effect, state_simp_rules] using savedU.sp
    · intro reg offset member
      simpa [t, u, Op.effect, state_simp_rules] using savedU.words reg offset member
    · intro reg low high
      simpa [t, u, Op.effect, state_simp_rules] using savedU.vectors reg low high
  have arguments : ∀ reg : BitVec 5, reg ∈ [0#5, 1#5, 2#5, 3#5, 4#5] →
      r (.GPR reg) t = r (.GPR reg) s := by
    intro reg member
    simpa [t, u, Op.effect, state_simp_rules] using
      (prologue_arguments u base).1 reg member
  have byte : r (.GPR 8#5) t = data[data.size - 1]!.toBitVec.setWidth 64 := by
    have loaded := prologue_loaded u base
    have last := last_byte t (r (.GPR 2#5) s) (r (.GPR 3#5) s) data
      owned.length nonempty inputs.input
    have loaded' : r (.GPR 8#5) t =
        (read_mem_bytes 1 (r (.GPR 2#5) s + (r (.GPR 3#5) s - 1#64)) t).setWidth 64 := by
      simpa [t, u, Op.effect, state_simp_rules] using loaded
    exact loaded'.trans (congrArg (BitVec.setWidth 64) last)
  have zeroByte :
      (data[data.size - 1]!.toBitVec.setWidth 64).setWidth 32 = 0#32 ↔
        data[data.size - 1]! = 0 := by
    have narrow : (data[data.size - 1]!.toBitVec.setWidth 64).setWidth 32 = 0#32 ↔
        data[data.size - 1]!.toBitVec = 0#8 := by bv_omega
    exact narrow.trans (by simpa only [UInt8.toBitVec_ofNat] using
      (UInt8.toBitVec_inj (a := data[data.size - 1]!) (b := 0)))
  refine ⟨t, nonempty_entry s base hc he ha hp nonzero, ?_⟩
  refine ⟨?_, ?_, ?_, saved, arguments, ?_, byte, ?_, frame, inputs⟩
  · simp only [t, u, block_program, Op.program]
  · simpa only [t, u, block_error, Op.error] using he
  · exact block_aligned base prologueOps u (Op.aligned .p0 base s ha)
  · simpa [t, u, Op.effect, state_simp_rules] using (prologue_arguments u base).2
  · have pcT : read_pc t = if (r (.GPR 8#5) t).setWidth 32 = 0#32
        then base + 184#64 else base + 64#64 := prologue_pc u base
    simp only [byte, zeroByte] at pcT
    exact pcT

end SszArm.Delimited
