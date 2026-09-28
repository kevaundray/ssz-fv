import SszArm.MeasureScalarByteReads

namespace SszArm.Measure.Scalar.Bytes

open Result
open SszNative (NatOperand)

def Kind.smallPC : Kind → Nat
  | .vector => 2316 | .list => 1960

def Kind.largePC : Kind → Nat
  | .vector => 1176 | .list => 816

def Kind.setupOps (kind : Kind) (size : BitVec 64) : List Op :=
  match kind with
  | .vector => [p1156, p1160, p1164, p1168, p1172]
  | .list => [p776, p780, p784, p788, p792, p796] ++
      (if size = 0#64 then [p800, p804] else [p808]) ++ [p812]

@[irreducible] def setupResult (kind : Kind) (s : ArmState) (size : BitVec 64) : ArmState :=
  effect (kind.setupOps size) s

private def setupTagOps : Kind → List Op
  | .vector => [p1156, p1160] | .list => [p776, p780]

private def setupReadOps : Kind → List Op
  | .vector => [p1164, p1168] | .list => [p784, p788]

private def setupFinishOps (kind : Kind) (size : BitVec 64) : List Op :=
  match kind with
  | .vector => [p1172]
  | .list => [p792, p796] ++ (if size = 0#64 then [p800, p804] else [p808]) ++ [p812]

@[irreducible] private def setupTagged (kind : Kind) (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.entry + 8))
    (write_pstate (AddWithCarry 2#32 (~~~2#32) 1#1).2 s)

@[irreducible] private def setupRead (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (kind.entry + 16))
    (match kind with
     | .vector => w (.GPR 20#5) size (w (.GPR 9#5) cap.payload (w (.GPR 8#5) cap.pointer s))
     | .list => w (.GPR 9#5) cap.payload (w (.GPR 8#5) cap.pointer (w (.GPR 20#5) size s)))

@[irreducible] private def setupFinished (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) : ArmState :=
  w .PC (base + BitVec.ofNat 64 (if cap.pointer = 0#64 then kind.smallPC else kind.largePC))
    (match kind with
     | .vector => s
     | .list => w (.GPR 10#5) (if size = 0#64 then 0#64 else 1#64)
         (write_pstate (AddWithCarry size (~~~0#64) 1#1).2 s))

private theorem setup_tag_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 2#32) :
    effect (setupTagOps kind) s = setupTagged kind s base := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [effect, setupTagOps, setupTagged, Kind.entry, p1156, p1160, p776, p780,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory, pc, tag, BitVec.add_assoc] <;>
    simp only [w, write_base_pc, write_base_flag]

private theorem setup_read_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 (kind.entry + 8))
    (pointer : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = cap.pointer)
    (payload : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = cap.payload)
    (actual : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = size) :
    effect (setupReadOps kind) s = setupRead kind s base cap size := by
  change r .PC s = _ at pc
  cases kind <;>
    simp (config := {decide := true, instances := true})
      [effect, setupReadOps, setupRead, Kind.entry, p1164, p1168, p784, p788,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       BoolCodec.pair_read_low, BoolCodec.pair_read_high, pointer, payload, actual,
       pc, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

@[irreducible] private def setupCompared (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 796#64) (write_pstate (AddWithCarry (r (.GPR 20#5) s) (~~~0#64) 1#1).2 s)

private def setupMarkerOps (size : BitVec 64) : List Op :=
  [p796] ++ if size = 0#64 then [p800, p804] else [p808]

@[irreducible] private def setupMarked (s : ArmState) (base size : BitVec 64) : ArmState :=
  w .PC (base + 812#64) (w (.GPR 10#5) (if size = 0#64 then 0#64 else 1#64) s)

private theorem setup_flags_pc (s : ArmState) (flags : PState) (pc : BitVec 64) :
    write_pstate flags (w .PC pc s) = w .PC pc (write_pstate flags s) := by
  simp only [write_pstate, w, write_base_pc, write_base_flag]

private theorem setup_compare_effect (s : ArmState) :
    p792.effect s = write_pstate
      (AddWithCarry (r (.GPR 20#5) s) (~~~0#64) 1#1).2
      (w .PC (r .PC s + 4#64) s) := by
  change exec_inst (.DPI (.Add_sub_imm
    { sf := 1, op := 1, S := 1, sh := 0, imm12 := 0, Rn := 20, Rd := 31 })) s = _
  simp (config := {decide := true, instances := true})
    [exec_inst, state_simp_rules, bitvec_rules, minimal_theory]

private theorem setup_compare_summary (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 792#64) : effect [p792] s = setupCompared s base := by
  change r .PC s = _ at pc
  change p792.effect s = _
  rw [setup_compare_effect, setup_flags_pc, pc]
  have nextPC : base + 792#64 + 4#64 = base + 796#64 := by bv_omega
  rw [nextPC]
  simp only [setupCompared]

private theorem setup_marker_summary (s : ArmState) (base size : BitVec 64)
    (pc : read_pc s = base + 796#64)
    (flag : r (.FLAG .Z) s = if size = 0#64 then 1#1 else 0#1) :
    effect (setupMarkerOps size) s = setupMarked s base size := by
  change r .PC s = _ at pc
  by_cases empty : size = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [effect, setupMarkerOps, setupMarked, p796, p800, p804, p808,
       Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
       pc, flag, empty, BitVec.add_assoc, NatExact.gpr_w_pc] <;>
    simp only [w, write_base_pc, write_base_gpr]

private theorem setup_list_cap_summary (s : ArmState) (base : BitVec 64) (cap : NatOperand)
    (pc : read_pc s = base + 812#64) (pointer : r (.GPR 8#5) s = cap.pointer) :
    effect [p812] s = w .PC (base + if cap.pointer = 0#64 then 1960#64 else 816#64) s := by
  change r .PC s = _ at pc
  by_cases small : cap.pointer = 0#64 <;>
    simp (config := {decide := true, instances := true})
      [effect, p812, Op.effect, exec_inst, state_simp_rules, bitvec_rules,
       minimal_theory, pc, pointer, small, BitVec.add_assoc]

private theorem setup_finish_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 (kind.entry + 16))
    (pointer : r (.GPR 8#5) s = cap.pointer) (actual : r (.GPR 20#5) s = size) :
    effect (setupFinishOps kind size) s = setupFinished kind s base cap size := by
  cases kind with
  | vector =>
    change r .PC s = base + 1172#64 at pc
    by_cases small : cap.pointer = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [effect, setupFinishOps, setupFinished, Kind.smallPC, Kind.largePC, p1172,
         Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         pc, pointer, small, BitVec.add_assoc]
  | list =>
    change read_pc s = base + 792#64 at pc
    have factor : effect (setupFinishOps .list size) s =
        effect [p812] (effect (setupMarkerOps size) (effect [p792] s)) := by
      by_cases empty : size = 0#64 <;> simp [setupFinishOps, setupMarkerOps, effect, empty]
    rw [factor, setup_compare_summary s base pc]
    have markerPC : read_pc (setupCompared s base) = base + 796#64 := by
      simp [setupCompared, state_simp_rules]
    have zeroFlag : (AddWithCarry size (~~~0#64) 1#1).2.z =
        if size = 0#64 then 1#1 else 0#1 := by
      by_cases empty : size = 0#64
      · simpa only [if_pos empty] using (Udivti3.cmp_zero size 0#64).mpr empty
      · simpa only [if_neg empty] using (Udivti3.cmp_nonzero size 0#64).mpr empty
    have markerFlag : r (.FLAG .Z) (setupCompared s base) =
        if size = 0#64 then 1#1 else 0#1 := by
      simpa [setupCompared, state_simp_rules, actual] using zeroFlag
    rw [setup_marker_summary _ base size markerPC markerFlag]
    have capPC : read_pc (setupMarked (setupCompared s base) base size) = base + 812#64 := by
      simp [setupMarked, state_simp_rules]
    have capPointer : r (.GPR 8#5) (setupMarked (setupCompared s base) base size) = cap.pointer := by
      simpa (config := {decide := true}) [setupMarked, setupCompared, state_simp_rules] using pointer
    rw [setup_list_cap_summary _ base cap capPC capPointer]
    by_cases small : cap.pointer = 0#64 <;>
      simp [setupFinished, setupMarked, setupCompared, Kind.smallPC, Kind.largePC,
        actual, small, NatExact.gpr_w_pc, w_of_w_shadow]


private structure SetupFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  memory : t.mem = s.mem
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 20#5] → r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

private theorem SetupFrame.trans {s t u : ArmState} (first : SetupFrame s t) (second : SetupFrame t u) :
    SetupFrame s u :=
  ⟨second.program.trans first.program, second.error.trans first.error,
   second.memory.trans first.memory,
   fun reg outside => (second.registers reg outside).trans (first.registers reg outside),
   fun reg => (second.vectors reg).trans (first.vectors reg)⟩

private theorem setup_tagged_frame (kind : Kind) (s : ArmState) (base : BitVec 64) :
    SetupFrame s (setupTagged kind s base) := by
  constructor
  · simp [setupTagged, state_simp_rules]
  · simp [setupTagged, state_simp_rules]
  · simp [setupTagged, state_simp_rules]
  · intro reg outside; simp [setupTagged, state_simp_rules]
  · intro reg; simp [setupTagged, state_simp_rules]

private theorem setup_read_frame (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) : SetupFrame s (setupRead kind s base cap size) := by
  constructor
  · cases kind <;> simp [setupRead, state_simp_rules]
  · cases kind <;> simp [setupRead, state_simp_rules]
  · cases kind <;> simp [setupRead, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    cases kind <;> simp [setupRead, NatExact.r_gpr_w, state_simp_rules,
      outside.1, outside.2.1, outside.2.2.2]
  · intro reg; cases kind <;> simp [setupRead, state_simp_rules]

private theorem setup_finished_frame (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) : SetupFrame s (setupFinished kind s base cap size) := by
  constructor
  · cases kind <;> simp [setupFinished, state_simp_rules]
  · cases kind <;> simp [setupFinished, state_simp_rules]
  · cases kind <;> simp [setupFinished, state_simp_rules]
  · intro reg outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    cases kind <;> simp [setupFinished, NatExact.r_gpr_w, state_simp_rules, outside.2.2.1]
  · intro reg; cases kind <;> simp [setupFinished, state_simp_rules]

private theorem setup_tagged_pc (kind : Kind) (s : ArmState) (base : BitVec 64) :
    read_pc (setupTagged kind s base) = base + BitVec.ofNat 64 (kind.entry + 8) := by
  unfold setupTagged
  simp only [read_pc, r_of_w_same]

private theorem setup_read_pc (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) :
    read_pc (setupRead kind s base cap size) = base + BitVec.ofNat 64 (kind.entry + 16) := by
  unfold setupRead
  simp only [read_pc, r_of_w_same]

private theorem setup_read_values (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) :
    r (.GPR 8#5) (setupRead kind s base cap size) = cap.pointer ∧
    r (.GPR 9#5) (setupRead kind s base cap size) = cap.payload ∧
    r (.GPR 20#5) (setupRead kind s base cap size) = size := by
  cases kind <;> simp (config := {decide := true}) [setupRead, state_simp_rules]

private theorem setup_finished_pc (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) :
    read_pc (setupFinished kind s base cap size) =
      base + BitVec.ofNat 64 (if cap.pointer = 0#64 then kind.smallPC else kind.largePC) := by
  unfold setupFinished
  simp only [read_pc, r_of_w_same]

private theorem setup_finished_register (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) (reg : BitVec 5) (outside : reg ≠ 10#5) :
    r (.GPR reg) (setupFinished kind s base cap size) = r (.GPR reg) s := by
  cases kind <;> simp [setupFinished, NatExact.r_gpr_w, state_simp_rules, outside]

private theorem setup_finished_marker (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) :
    r (.GPR 10#5) (setupFinished .list s base cap size) = if size = 0#64 then 0#64 else 1#64 := by
  simp (config := {decide := true}) [setupFinished, state_simp_rules]

private theorem setup_effects (first second third : List Op) (s t u v : ArmState)
    (hfirst : effect first s = t) (hsecond : effect second t = u) (hthird : effect third u = v) :
    effect (first ++ second ++ third) s = v := by
  simp only [effect, List.foldl_append]
  change effect third (effect second (effect first s)) = v
  exact (congrArg (fun state => effect third (effect second state)) hfirst).trans
    ((congrArg (effect third) hsecond).trans hthird)


private theorem setup_summary (kind : Kind) (s : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 2#32)
    (pointer : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = cap.pointer)
    (payload : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = cap.payload)
    (actual : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = size) :
    setupResult kind s size =
      setupFinished kind (setupRead kind (setupTagged kind s base) base cap size) base cap size := by
  have factor : kind.setupOps size = setupTagOps kind ++ setupReadOps kind ++ setupFinishOps kind size := by
    cases kind <;> by_cases zero : size = 0#64 <;>
      simp [Kind.setupOps, setupFinishOps, setupReadOps, setupTagOps, zero]
  let u := setupTagged kind s base
  let v := setupRead kind u base cap size
  let t := setupFinished kind v base cap size
  have frame : SetupFrame s u := setup_tagged_frame kind s base
  have reads (n : Nat) (address : BitVec 64) : read_mem_bytes n address u = read_mem_bytes n address s := by
    exact BoolCodec.read_bytes_congr u s n address (by intro i hi; exact congrFun frame.memory _)
  have ptr : read_mem_bytes 8 (r (.GPR 1#5) u + 8#64) u = cap.pointer := by
    rw [frame.registers _ (by decide), reads]; exact pointer
  have pay : read_mem_bytes 8 (r (.GPR 1#5) u + 16#64) u = cap.payload := by
    rw [frame.registers _ (by decide), reads]; exact payload
  have len : read_mem_bytes 8 (r (.GPR 21#5) u + 16#64) u = size := by
    rw [frame.registers _ (by decide), reads]; exact actual
  have first : effect (setupTagOps kind) s = u := setup_tag_summary kind s base pc tag
  have second : effect (setupReadOps kind) u = v := setup_read_summary kind u base cap size
    (setup_tagged_pc kind s base) ptr pay len
  have values := setup_read_values kind u base cap size
  have third : effect (setupFinishOps kind size) v = t := setup_finish_summary kind v base cap size
    (setup_read_pc kind u base cap size) values.1 values.2.2
  have complete := setup_effects (setupTagOps kind) (setupReadOps kind) (setupFinishOps kind size)
    s u v t first second third
  simpa only [setupResult, factor] using complete




structure Setup (kind : Kind) (s t : ArmState) (base : BitVec 64)
    (cap : NatOperand) (size : BitVec 64) : Prop where
  pc : read_pc t = base + BitVec.ofNat 64
    (if cap.pointer = 0#64 then kind.smallPC else kind.largePC)
  pointer : r (.GPR 8#5) t = cap.pointer
  payload : r (.GPR 9#5) t = cap.payload
  actual : r (.GPR 20#5) t = size
  marker : kind = .list → r (.GPR 10#5) t = if size = 0#64 then 0#64 else 1#64
  program : t.program = s.program
  error : read_err t = read_err s
  memory : t.mem = s.mem
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 9#5, 10#5, 20#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem setup_run (kind : Kind) (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None)
    (pc : read_pc s = base + BitVec.ofNat 64 kind.entry)
    (tag : (r (.GPR 8#5) s).setWidth 32 = 2#32)
    (cap : NatOperand) (size : BitVec 64)
    (pointer : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = cap.pointer)
    (payload : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = cap.payload)
    (actual : read_mem_bytes 8 (r (.GPR 21#5) s + 16#64) s = size) :
    run (kind.setupOps size).length s = setupResult kind s size ∧
      Setup kind s (setupResult kind s size) base cap size := by
  have follows : Follows base (kind.setupOps size) s := by
    change r .PC s = _ at pc
    change r .ERR s = _ at error
    have zeroFlag := Udivti3.cmp_zero size 0#64
    have nonzeroFlag := Udivti3.cmp_nonzero size 0#64
    cases kind <;> by_cases zero : size = 0#64 <;>
      simp (config := {decide := true, instances := true})
        [Kind.setupOps, Kind.entry, Follows, p1156, p1160, p1164, p1168, p1172,
         p776, p780, p784, p788, p792, p796, p800, p804, p808, p812,
         Op.effect, exec_inst, state_simp_rules, bitvec_rules, minimal_theory,
         BoolCodec.pair_read_low, BoolCodec.pair_read_high, BitVec.add_assoc,
         pc, error, tag, pointer, payload, actual, zero, zeroFlag, nonzeroFlag]
  refine ⟨?_, ?_⟩
  · simpa only [setupResult] using runs _ s base code follows
  rw [setup_summary kind s base cap size pc tag pointer payload actual]
  let u := setupTagged kind s base
  let v := setupRead kind u base cap size
  let t := setupFinished kind v base cap size
  have frame : SetupFrame s t := (setup_tagged_frame kind s base).trans
    ((setup_read_frame kind u base cap size).trans (setup_finished_frame kind v base cap size))
  have values := setup_read_values kind u base cap size
  refine ⟨setup_finished_pc kind v base cap size, ?_, ?_, ?_, ?_,
    frame.program, frame.error, frame.memory, frame.registers, frame.vectors⟩
  · exact (setup_finished_register kind v base cap size _ (by decide)).trans values.1
  · exact (setup_finished_register kind v base cap size _ (by decide)).trans values.2.1
  · exact (setup_finished_register kind v base cap size _ (by decide)).trans values.2.2
  · intro list
    subst kind
    exact setup_finished_marker v base cap size



end SszArm.Measure.Scalar.Bytes
