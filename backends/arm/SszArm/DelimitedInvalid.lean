import SszArm.DelimitedValidation
import SszArm.DelimitedTailContracts

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem Owned.tail_owned {s u : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) (nonempty : r (.GPR 3#5) s ≠ 0#64)
    (out : r (.GPR 0#5) u = r (.GPR 0#5) s)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64) : TailOwned u := by
  have stack := owned.stackBound
  simp only [activationSpan, nonempty, ↓reduceIte] at stack
  have apart : (r (.GPR 0#5) s).toNat + 76 ≤ (r (.GPR 31#5) s).toNat - 112 ∨
      (r (.GPR 31#5) s).toNat ≤ (r (.GPR 0#5) s).toNat := by
    rcases owned.outputStack with impossible | separate
    · omega
    · have interval := separate (activationSpan s) (by simp)
      simp only [activationSpan, nonempty, ↓reduceIte] at interval
      omega
  have bound := (r (.GPR 31#5) s).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · bv_omega
  · bv_omega
  · simpa only [out] using owned.outputBound
  · simp only [out, sp]
    bv_omega
  · simp only [out, sp]
    bv_omega

/-- Lift a returning tail's output/lowering frame into the original activation. -/
theorem tail_frame_local {s u t : ArmState} {limit : Option Nat} {data : Ssz.Bytes}
    (owned : Owned s limit data) (nonempty : r (.GPR 3#5) s ≠ 0#64)
    (out : r (.GPR 0#5) u = r (.GPR 0#5) s)
    (sp : r (.GPR 31#5) u = r (.GPR 31#5) s - 96#64)
    (frame : MemoryFrame (tailWrites u) u t) : MemoryFrame (localWrites s) u t := by
  have stack := owned.stackBound
  simp only [activationSpan, nonempty, ↓reduceIte] at stack
  have spNat : (r (.GPR 31#5) u).toNat = (r (.GPR 31#5) s).toNat - 96 := by bv_omega
  intro a outside
  apply frame a
  intro span member
  simp only [tailWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simpa only [out] using outside ((r (.GPR 0#5) s).toNat, 76) (by simp [localWrites])
  · have activation := outside (activationSpan s) (by simp [localWrites])
    simp only [activationSpan, nonempty, ↓reduceIte] at activation
    simp only [spNat]
    omega

private def reasonOps (allZero : Bool) : List Op :=
  if allZero then noDelimiterOps else trailingOps

private theorem reason_run (allZero : Bool) (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = if allZero then base + 188#64 else base + 616#64) :
    run (if allZero then 2 else 1) s = block base (reasonOps allZero) s := by
  cases allZero with
  | false => exact trailing_run s base hc he ha hp
  | true => exact noDelimiter_run s base hc he ha hp

private theorem reason_register (allZero : Bool) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (unchanged : reg ≠ 9#5) :
    r (.GPR reg) (block base (reasonOps allZero) s) = r (.GPR reg) s := by
  cases allZero <;> simp [reasonOps, noDelimiterOps, trailingOps, block, Op.effect,
    put, next, state_simp_rules, unchanged]

private theorem reason_memory (allZero : Bool) (s : ArmState) (base : BitVec 64) :
    (block base (reasonOps allZero) s).mem = s.mem := by
  cases allZero <;> simp [reasonOps, noDelimiterOps, trailingOps, block, Op.effect,
    put, next, state_simp_rules]

private theorem reason_vectors (allZero : Bool) (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) :
    r (.SFP reg) (block base (reasonOps allZero) s) = r (.SFP reg) s := by
  cases allZero <;> simp [reasonOps, noDelimiterOps, trailingOps, block, Op.effect,
    put, next, state_simp_rules]

private theorem reason_values (allZero : Bool) (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = if allZero then base + 188#64 else base + 616#64) :
    read_pc (block base (reasonOps allZero) s) = base + 620#64 ∧
      (r (.GPR 9#5) (block base (reasonOps allZero) s)).setWidth 32 =
        (if allZero then 17#32 else 18#32) := by
  have pc : r .PC s = if allZero then base + 188#64 else base + 616#64 := hp
  cases allZero <;> simp [reasonOps, noDelimiterOps, trailingOps, block, Op.effect,
    put, next, state_simp_rules, pc, BitVec.add_assoc]

/-- A zero final byte executes the complete real scan and error RET. The model's
validation error has priority over both allocation and the optional Nat limit. -/
theorem invalid_model_correct (s : ArmState) (base : BitVec 64) (limit : Option Nat)
    (data : Ssz.Bytes) (owned : Owned s limit data)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + BitVec.ofNat 64 entry)
    (nonempty : 0 < data.size) (delimiter : data[data.size - 1]! = 0) :
    ∃ fuel t, run fuel s = t ∧ Post s t limit data := by
  obtain ⟨u, entered, start⟩ := nonempty_start s base limit data owned hc he ha hp nonempty
  have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
    have length := owned.length
    bv_omega
  have codeU : CodeAt u base := by simpa only [CodeAt, start.program] using hc
  have length : r (.GPR 3#5) u = BitVec.ofNat 64 (scanData data).length := by
    rw [start.arguments 3#5 (by simp)]
    apply BitVec.eq_of_toNat_eq
    simp [scanData, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.physical, owned.length]
  have bytes : ScanBytes u (r (.GPR 2#5) u) (scanData data) :=
    bytes_to_scan u _ data (by simpa only [start.arguments 2#5 (by simp)] using start.inputs.input)
  obtain ⟨fuel, v, scanned, scanFrame, scanPc⟩ := zero_scan base (scanData data) u codeU
    start.error start.aligned (by simpa only [delimiter, ↓reduceIte] using start.pc)
    length (by simpa [scanData] using owned.physical) bytes
  have pcV : read_pc v = if data.all (· == 0) then base + 188#64 else base + 616#64 := by
    simpa only [scan_data_all] using scanPc
  let w := block base (reasonOps (data.all (· == 0))) v
  have codeV : CodeAt v base := by simpa only [CodeAt, scanFrame.program] using codeU
  have errorV : read_err v = .None := scanFrame.error.trans start.error
  have alignV : CheckSPAlignment v := scanFrame.aligned start.aligned
  have reason := reason_run (data.all (· == 0)) v base codeV errorV alignV pcV
  have values := reason_values (data.all (· == 0)) v base pcV
  have same : w.mem = u.mem := (reason_memory _ v base).trans scanFrame.memory
  have spU : r (.GPR 31#5) w = r (.GPR 31#5) u :=
    (reason_register _ v base 31#5 (by decide)).trans (scanFrame.registers 31#5 (by decide))
  have out : r (.GPR 0#5) w = r (.GPR 0#5) s :=
    (reason_register _ v base 0#5 (by decide)).trans
      ((scanFrame.registers 0#5 (by decide)).trans (start.arguments 0#5 (by simp)))
  have sp : r (.GPR 31#5) w = r (.GPR 31#5) s - 96#64 := spU.trans start.saved.sp
  have saved : Saved s w := by
    refine ⟨sp, ?_, ?_⟩
    · intro reg offset member
      rw [spU, (Memory.mem_eq_iff_read_mem_bytes_eq.mp same) 8]
      exact start.saved.words reg offset member
    · intro reg low high
      rw [reason_vectors, scanFrame.vectors]
      exact start.saved.vectors reg low high
  have ownership : TailOwned w := owned.tail_owned nonzero out sp
  have returned := tail_run_returned .invalid s w base
    (by simpa only [w, CodeAt, block_program] using codeV)
    ((block_error base (reasonOps (data.all (· == 0))) v).trans errorV)
    (block_aligned base (reasonOps (data.all (· == 0))) v alignV) values.1 saved ownership
  let t := tailResult .invalid base w
  have before : MemoryFrame (localWrites s) s w := start.frame.trans (by
    intro address outside
    exact congrFun same address)
  have frame : MemoryFrame (localWrites s) s t := before.trans
    (tail_frame_local owned nonzero out sp (tailMemoryFrame .invalid w base ownership))
  have image := invalid_tail_image w base ownership
  have reasonWord : (r (.GPR 9#5) w).setWidth 32 =
      (if data.all (· == 0) then 17#32 else 18#32) := values.2
  rw [reasonWord] at image
  have emptyFalse : ¬ data.size = 0 := by omega
  have cursor := frame.load ((r (.GPR 4#5) s).toNat + 16) 8 (by
      have bound := owned.arenaBound
      omega) (owned.arenaLocal.subspan 16 8 (by decide))
  refine ⟨16 + fuel + (if data.all (· == 0) then 2 else 1) + 25, t, ?_, ?_⟩
  · rw [run_plus, run_plus, run_plus, entered, scanned, reason]
    exact returned.1
  · apply post_of_frame s t limit data owned returned.2
    · cases allZero : data.all (· == 0) <;>
        simpa [t, SszNative.Delimited.run, SszNative.Delimited.validate, emptyFalse,
          delimiter, SszNative.Delimited.scanZeros, allZero, SszNative.Delimited.ResultAt,
          SszNative.BitView.ResultAt, out] using image
    · cases allZero : data.all (· == 0) <;>
        simp [SszNative.Delimited.run, SszNative.Delimited.validate, emptyFalse,
          delimiter, SszNative.Delimited.scanZeros, allZero,
          SszNative.Delimited.Outcome.PreparedAt]
    · have observed := Option.some.inj cursor
      cases allZero : data.all (· == 0) <;>
        simpa [SszNative.Delimited.run, SszNative.Delimited.validate, emptyFalse,
          delimiter, SszNative.Delimited.scanZeros, allZero, arenaOf, widthLoad,
          BitVec.ofNat_add, BitVec.ofNat_toNat] using observed
    · cases allZero : data.all (· == 0) <;>
        simpa [SszNative.Delimited.run, SszNative.Delimited.validate, emptyFalse,
          delimiter, SszNative.Delimited.scanZeros, allZero,
          SszNative.Delimited.Outcome.allocation, writesFor] using frame

end SszArm.Delimited
