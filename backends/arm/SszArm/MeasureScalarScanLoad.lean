import SszArm.MeasureScalarByteOps
import SszArm.UintShifts

namespace SszArm.Measure.Scalar.Bytes

open Result

inductive Kind where
  | vector | list
  deriving DecidableEq

def Kind.scanLoad : Kind → Nat
  | .vector => 1188 | .list => 828

def Kind.scanGuard : Kind → Nat
  | .vector => 1180 | .list => 820

def Kind.scanTail : Kind → Nat
  | .vector => 1220 | .list => 860

def Kind.scanExit : Kind → Nat
  | .vector => 1232 | .list => 868

def Kind.scanZero : Kind → Nat
  | .vector => 2852 | .list => 2328

def Kind.loadOps : Kind → List Op
  | .vector => [p1188, p1192, p1196, p1200, p1204, p1208, p1212, p1216]
  | .list => [p828, p832, p836, p840, p844, p848, p852, p856]

@[irreducible] def scanLoadResult (kind : Kind) (s : ArmState) (base limb : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 kind.scanTail)
    (w (.GPR 12#5) limb (NatCompare.saved s 9#5))

private def scanSpillOps : Kind → List Op
  | .vector => [p1188, p1192] | .list => [p828, p832]

private def scanReadOps : Kind → List Op
  | .vector => [p1196, p1200, p1204, p1208] | .list => [p836, p840, p844, p848]

private def scanReloadOps : Kind → List Op
  | .vector => [p1212, p1216] | .list => [p852, p856]

@[irreducible] private def scanSpilled (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.scanLoad + 8))
    (w (.GPR 31#5) (r (.GPR 31#5) s - 16#64) (NatCompare.saved s 9#5))

@[irreducible] private def scanRead (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  let address := r (.GPR 8#5) s + (r (.GPR 11#5) s <<< 3)
  w .PC (base + BitVec.ofNat 64 (kind.scanTail - 8))
    (w (.GPR 12#5) (read_mem_bytes 8 address s) (w (.GPR 9#5) address s))

@[irreducible] private def scanReloaded (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 kind.scanTail)
    (w (.GPR 31#5) (r (.GPR 31#5) s + 16#64)
      (w (.GPR 9#5) (read_mem_bytes 8 (r (.GPR 31#5) s) s) s))

private theorem scan_spill_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 kind.scanLoad) :
    effect (scanSpillOps kind) s = scanSpilled kind s base := by
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [effect, scanSpillOps, scanSpilled, Kind.scanLoad, NatCompare.saved,
       p1188, p1192, p828, p832, Op.effect, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, pc, lower, BitVec.add_assoc,
       NatExact.store_w, NatExact.gpr_w_pc] <;>
    simp only [Memory.write_mem_bytes_eq_mem_write_bytes, w, write_base_pc, write_base_gpr]

private theorem scan_read_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 (kind.scanLoad + 8)) :
    effect (scanReadOps kind) s = scanRead kind s base := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [effect, scanReadOps, scanRead, Kind.scanLoad, Kind.scanTail,
       p1196, p1200, p1204, p1208, p836, p840, p844, p848,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pc, BitVec.add_assoc, UintCodec.uint_lsl3_mask, UintCodec.uint_and_ones, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scan_reload_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + BitVec.ofNat 64 (kind.scanTail - 8)) :
    effect (scanReloadOps kind) s = scanReloaded kind s base := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [effect, scanReloadOps, scanReloaded, Kind.scanTail, p1212, p1216, p852, p856,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pc, aligned, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem scan_scratch_restore (s : ArmState) (limb pointer stack : BitVec 64) :
    w (.GPR 31#5) (r (.GPR 31#5) s)
      (w (.GPR 9#5) (r (.GPR 9#5) s)
        (w (.GPR 12#5) limb (w (.GPR 9#5) pointer (w (.GPR 31#5) stack s)))) =
      w (.GPR 12#5) limb s := by
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases isNine : reg = 9#5 <;> by_cases isTwelve : reg = 12#5 <;>
        by_cases isSP : reg = 31#5 <;> (try subst reg) <;>
        simp_all [NatExact.r_gpr_w, state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro bytes address; simp [state_simp_rules]

private theorem scan_assemble (kind : Kind) (s : ArmState) (base limb : BitVec 64)
    (loaded : read_mem_bytes 8 (r (.GPR 8#5) s + (r (.GPR 11#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb)
    (restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s) :
    scanReloaded kind (scanRead kind (scanSpilled kind s base) base) base =
      scanLoadResult kind s base limb := by
  have bridge := congrArg (w .PC (base + BitVec.ofNat 64 kind.scanTail))
    (scan_scratch_restore (NatCompare.saved s 9#5) limb
      (r (.GPR 8#5) s + (r (.GPR 11#5) s <<< 3)) (r (.GPR 31#5) s - 16#64))
  simp only [NatCompare.saved] at loaded restored
  simpa (config := {decide := true})
    [scanReloaded, scanRead, scanSpilled, scanLoadResult, NatCompare.saved,
     state_simp_rules, NatExact.gpr_w_pc, NatExact.store_w, BitVec.sub_add_cancel,
     loaded, restored] using bridge


theorem scan_load_run (kind : Kind) (s : ArmState) (base limb : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.scanLoad)
    (stackLow : 16 ≤ (r (.GPR 31#5) s).toNat)
    (loaded : read_mem_bytes 8 (r (.GPR 8#5) s + (r (.GPR 11#5) s <<< 3))
      (NatCompare.saved s 9#5) = limb) :
    run 8 s = scanLoadResult kind s base limb := by
  have restored : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64)
      (NatCompare.saved s 9#5) = r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have stack := BoolCodec.stack_aligned s aligned
  change Aligned (r (.GPR 31#5) s) 4 at stack
  have lower := BoolCodec.aligned_sub16 _ stack
  change r .PC s = _ at pc
  change r .ERR s = _ at error
  have follows : Follows base kind.loadOps s := by
    cases kind <;>
      simp (config := {decide := true, instances := true})
        [Kind.loadOps, Kind.scanLoad, Follows, p1188, p1192, p1196, p1200,
         p1204, p1208, p1212, p1216, p828, p832, p836, p840, p844, p848, p852, p856,
         Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         pc, error, lower, BitVec.add_assoc]
  rw [show 8 = kind.loadOps.length by cases kind <;> rfl, runs _ s base code follows]
  have factor : effect kind.loadOps s =
      effect (scanReloadOps kind) (effect (scanReadOps kind) (effect (scanSpillOps kind) s)) := by
    cases kind <;> rfl
  rw [factor, scan_spill_summary kind s base aligned pc]
  have spilledPC : read_pc (scanSpilled kind s base) = base + BitVec.ofNat 64 (kind.scanLoad + 8) := by
    simp [scanSpilled, state_simp_rules]
  rw [scan_read_summary kind _ base spilledPC]
  have readPC : read_pc (scanRead kind (scanSpilled kind s base) base) =
      base + BitVec.ofNat 64 (kind.scanTail - 8) := by simp [scanRead, state_simp_rules]
  have readAligned : CheckSPAlignment (scanRead kind (scanSpilled kind s base) base) := by
    simpa (config := {decide := true})
      [scanRead, scanSpilled, NatCompare.saved, CheckSPAlignment, state_simp_rules] using lower
  rw [scan_reload_summary kind _ base readAligned readPC]
  exact scan_assemble kind s base limb loaded restored


theorem scan_load_frame (kind : Kind) (s : ArmState) (base limb : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    NatNarrow.Frame s (scanLoadResult kind s base limb) := by
  have frame := NatNarrow.saved_frame s 9#5 stack
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [scanLoadResult, state_simp_rules] using frame.program
  · simpa [scanLoadResult, state_simp_rules] using frame.error
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp (disch := simp_all) [scanLoadResult, NatCompare.saved, state_simp_rules]
  · intro reg; simpa [scanLoadResult, state_simp_rules] using frame.vectors reg
  · intro address outside
    simpa [scanLoadResult, state_simp_rules] using frame.memory address outside

end SszArm.Measure.Scalar.Bytes
