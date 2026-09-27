import SszArm.UintShifts
import SszArm.UintWidthMemory

namespace SszArm.UintCodec

open SszNative.Limbs

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- The remaining literal instructions of the linked width prefix. Header,
Small and the final equality test are reused from UintExec. -/
inductive WidthOp where
  | subCount | testCount | endCount | subSp | save | index | scale | address
  | load | restore | addSp | remember | decrement | zero | increment | compareThree
  | belowThree | reject | empty | low | compareTwo | belowTwo | high | pair
  | oneHigh | onePair | emptyHigh | emptyLow
  deriving DecidableEq

def WidthOp.row : WidthOp → Nat × BitVec 32
  | .subCount => (156, 0xd100052b#32)
  | .testCount => (160, 0xb100057f#32)
  | .endCount => (164, 0x54006f40#32)
  | .subSp => (168, 0xd10043ff#32)
  | .save => (172, 0xf90003e9#32)
  | .index => (176, 0xaa0b03e9#32)
  | .scale => (180, 0xd37df129#32)
  | .address => (184, 0x8b090109#32)
  | .load => (188, 0xf940012c#32)
  | .restore => (192, 0xf94003e9#32)
  | .addSp => (196, 0x910043ff#32)
  | .remember => (200, 0xaa0b03ea#32)
  | .decrement => (204, 0xd100056b#32)
  | .zero => (208, 0xb4fffe8c#32)
  | .increment => (212, 0x9100054a#32)
  | .compareThree => (216, 0xf1000d5f#32)
  | .belowThree => (220, 0x54006da3#32)
  | .reject => (224, 0x14000438#32)
  | .empty => (3724, 0xb4001209#32)
  | .low => (3728, 0xf940010a#32)
  | .compareTwo => (3732, 0xf100093f#32)
  | .belowTwo => (3736, 0x54000a63#32)
  | .high => (3740, 0xf940050b#32)
  | .pair => (3744, 0x1400008d#32)
  | .oneHigh => (4068, 0xaa1f03eb#32)
  | .onePair => (4072, 0x1400003b#32)
  | .emptyHigh => (4300, 0xaa1f03eb#32)
  | .emptyLow => (4304, 0xaa1f03ea#32)

private def wn (s : ArmState) : ArmState := w .PC (read_pc s + 4#64) s
private def wp (reg : BitVec 5) (v : BitVec 64) (s : ArmState) : ArmState :=
  w (.GPR reg) v (wn s)

def WidthOp.effect (base : BitVec 64) : WidthOp → ArmState → ArmState
  | .subCount, s => wp 11 (r (.GPR 9#5) s - 1#64) s
  | .testCount, s => write_pstate (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2 (wn s)
  | .endCount, s => w .PC (if r (.FLAG .Z) s = 1#1 then base + 3724#64 else base + 168#64) s
  | .subSp, s => wp 31 (r (.GPR 31#5) s - 16#64) s
  | .save, s => w .PC (read_pc s + 4#64) (write_mem_bytes 8 (r (.GPR 31#5) s) (r (.GPR 9#5) s) s)
  | .index, s => wp 9 (r (.GPR 11#5) s) s
  | .scale, s => wp 9 (r (.GPR 9#5) s <<< 3) s
  | .address, s => wp 9 (r (.GPR 8#5) s + r (.GPR 9#5) s) s
  | .load, s => wp 12 (read_mem_bytes 8 (r (.GPR 9#5) s) s) s
  | .restore, s => wp 9 (read_mem_bytes 8 (r (.GPR 31#5) s) s) s
  | .addSp, s => wp 31 (r (.GPR 31#5) s + 16#64) s
  | .remember, s => wp 10 (r (.GPR 11#5) s) s
  | .decrement, s => wp 11 (r (.GPR 11#5) s - 1#64) s
  | .zero, s => w .PC (if r (.GPR 12#5) s = 0#64 then base + 160#64 else base + 212#64) s
  | .increment, s => wp 10 (r (.GPR 10#5) s + 1#64) s
  | .compareThree, s => Udivti3.compare (r (.GPR 10#5) s) 3#64 s
  | .belowThree, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 224#64 else base + 3728#64) s
  | .reject, s => w .PC (base + 4544#64) s
  | .empty, s => w .PC (if r (.GPR 9#5) s = 0#64 then base + 4300#64 else base + 3728#64) s
  | .low, s => wp 10 (read_mem_bytes 8 (r (.GPR 8#5) s) s) s
  | .compareTwo, s => Udivti3.compare (r (.GPR 9#5) s) 2#64 s
  | .belowTwo, s => w .PC (if r (.FLAG .C) s = 1#1 then base + 3740#64 else base + 4068#64) s
  | .high, s => wp 11 (read_mem_bytes 8 (r (.GPR 8#5) s + 8#64) s) s
  | .pair, s => w .PC (base + 4308#64) s
  | .oneHigh, s => wp 11 0#64 s
  | .onePair, s => w .PC (base + 4308#64) s
  | .emptyHigh, s => wp 11 0#64 s
  | .emptyLow, s => wp 10 0#64 s

/-- Every effect below is obtained from the real fetched and decoded opcode. -/
theorem width_step (s : ArmState) (base : BitVec 64) (op : WidthOp)
    (hc : CodeAt s base) (hp : read_pc s = base + BitVec.ofNat 64 op.row.1)
    (he : read_err s = .None) (ha : CheckSPAlignment s) :
    stepi s = op.effect base s := by
  have hm : op.row ∈ program := by cases op <;> decide
  have hf := hc op.row hm
  cases op
  all_goals
    simp only [WidthOp.row] at hp hf
    rw [stepi_eq_of_fetch_inst_of_decode_raw_inst s _ _ _ he hp
      (fetch_inst_from_program.trans hf) rfl]
    change r .PC s = _ at hp
    simp (config := {decide := true, instances := true})
      [WidthOp.effect, wp, wn, Udivti3.compare, Udivti3.next, exec_inst,
       state_simp_rules, bitvec_rules, minimal_theory, BitVec.setWidth_eq,
       BitVec.sub_eq_add_neg, ha, hp, BitVec.add_assoc, apply_ite, uint_lsl3_mask,
       uint_and_ones]
  all_goals first
    | rfl
    | exact w_of_w_commute (by decide)
    | (split <;> simp_all)
    | simp [w, write_base_pc, write_base_gpr]

theorem WidthOp.program (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    (op.effect base s).program = s.program := by
  cases op <;> simp [WidthOp.effect, wp, wn, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem WidthOp.error (op : WidthOp) (base : BitVec 64) (s : ArmState) :
    read_err (op.effect base s) = read_err s := by
  cases op <;> simp [WidthOp.effect, wp, wn, Udivti3.compare, Udivti3.next, state_simp_rules]

theorem WidthOp.aligned (op : WidthOp) (base : BitVec 64) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (op.effect base s) := by
  cases op <;> simp [WidthOp.effect, wp, wn, Udivti3.compare, Udivti3.next, state_simp_rules, ha]
  · exact BoolCodec.aligned_sub16 _ (BoolCodec.stack_aligned s ha)
  · exact BoolCodec.aligned_add16 _ (BoolCodec.stack_aligned s ha)

def widthBlock (base : BitVec 64) (ops : List WidthOp) (s : ArmState) : ArmState :=
  ops.foldl (fun t op => op.effect base t) s

def WidthFollows (base : BitVec 64) : List WidthOp → ArmState → Prop
  | [], _ => True
  | op :: ops, s => read_pc s = base + BitVec.ofNat 64 op.row.1 ∧
      WidthFollows base ops (op.effect base s)

theorem widthBlock_run (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : WidthFollows base ops s) : run ops.length s = widthBlock base ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    change run (ops.length + 1) s = widthBlock base ops (op.effect base s)
    rw [run, width_step s base op hc hf.1 he ha]
    exact ih _ (by simpa only [CodeAt, WidthOp.program] using hc)
      (by simpa only [WidthOp.error] using he) (op.aligned base s ha) hf.2

/-- Finite actual execution; fuel is composed rather than guessed. -/
def WidthRuns (s : ArmState) (P : ArmState → Prop) : Prop := ∃ fuel, P (run fuel s)

theorem WidthRuns.done (s : ArmState) (P : ArmState → Prop) (h : P s) : WidthRuns s P :=
  ⟨0, h⟩

theorem WidthRuns.prefix {s t : ArmState} {P : ArmState → Prop} (n : Nat)
    (h : run n s = t) (ht : WidthRuns t P) : WidthRuns s P := by
  rcases ht with ⟨fuel, hf⟩
  exact ⟨n + fuel, by simpa only [run_plus, h] using hf⟩

private theorem widthBlock_cps (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hf : WidthFollows base ops s) (P : ArmState → Prop)
    (ht : WidthRuns (widthBlock base ops s) P) : WidthRuns s P :=
  WidthRuns.prefix ops.length (widthBlock_run base ops s hc he ha hf) ht

private theorem widthBlock_program (base : BitVec 64) (ops : List WidthOp) (s : ArmState) :
    (widthBlock base ops s).program = s.program := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.program base s)

private theorem widthBlock_error (base : BitVec 64) (ops : List WidthOp) (s : ArmState) :
    read_err (widthBlock base ops s) = read_err s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => exact (ih _).trans (op.error base s)

private theorem widthBlock_aligned (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (ha : CheckSPAlignment s) : CheckSPAlignment (widthBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact ha
  | cons op ops ih => exact ih _ (op.aligned base s ha)

private theorem width_count_z (x : BitVec 64) :
    (AddWithCarry x 1#64 0#1).2.z = 1#1 ↔ x + 1#64 = 0#64 := by
  change (if (AddWithCarry x 1#64 0#1).1 = 0#64 then 1#1 else 0#1) = 1#1 ↔ _
  rw [fst_AddWithCarry_eq_add]
  simp

private theorem width_pc_frame (s : ArmState) (pc : BitVec 64) : WidthFrame s (w .PC pc s) := by
  constructor <;> simp [state_simp_rules]

private theorem width_compare_frame (s : ArmState) (a b : BitVec 64) :
    WidthFrame s (Udivti3.compare a b s) := by
  constructor <;> simp [Udivti3.compare, Udivti3.next, state_simp_rules]

private theorem width_put_frame (s : ArmState) (reg : BitVec 5) (v : BitVec 64)
    (hr : reg ∈ [8#5, 9#5, 10#5, 11#5, 12#5]) : WidthFrame s (wp reg v s) := by
  constructor
  · simp [wp, wn, state_simp_rules]
  · simp [wp, wn, state_simp_rules]
  · intro r hr'
    have hne : r ≠ reg := by intro h; subst r; exact hr' hr
    simp [wp, wn, state_simp_rules, hne]
  · intro r; simp [wp, wn, state_simp_rules]
  · intro a ha; simp [wp, wn, state_simp_rules]

private theorem width_pstate_frame (s : ArmState) (flags : PState) :
    WidthFrame s (write_pstate flags (wn s)) := by
  constructor <;> simp [wn, state_simp_rules]

private theorem widthOp_readonly_frame (base : BitVec 64) (op : WidthOp) (s : ArmState)
    (hsub : op ≠ .subSp) (hsave : op ≠ .save)
    (hrestore : op ≠ .restore) (hadd : op ≠ .addSp) :
    WidthFrame s (op.effect base s) := by
  cases op with
  | subCount => exact width_put_frame s 11#5 _ (by decide)
  | testCount => exact width_pstate_frame s _
  | endCount => exact width_pc_frame s _
  | subSp => exact False.elim (hsub rfl)
  | save => exact False.elim (hsave rfl)
  | index => exact width_put_frame s 9#5 _ (by decide)
  | scale => exact width_put_frame s 9#5 _ (by decide)
  | address => exact width_put_frame s 9#5 _ (by decide)
  | load => exact width_put_frame s 12#5 _ (by decide)
  | restore => exact False.elim (hrestore rfl)
  | addSp => exact False.elim (hadd rfl)
  | remember => exact width_put_frame s 10#5 _ (by decide)
  | decrement => exact width_put_frame s 11#5 _ (by decide)
  | zero => exact width_pc_frame s _
  | increment => exact width_put_frame s 10#5 _ (by decide)
  | compareThree => exact width_compare_frame s _ _
  | belowThree => exact width_pc_frame s _
  | reject => exact width_pc_frame s _
  | empty => exact width_pc_frame s _
  | low => exact width_put_frame s 10#5 _ (by decide)
  | compareTwo => exact width_compare_frame s _ _
  | belowTwo => exact width_pc_frame s _
  | high => exact width_put_frame s 11#5 _ (by decide)
  | pair => exact width_pc_frame s _
  | oneHigh => exact width_put_frame s 11#5 _ (by decide)
  | onePair => exact width_pc_frame s _
  | emptyHigh => exact width_put_frame s 11#5 _ (by decide)
  | emptyLow => exact width_put_frame s 10#5 _ (by decide)

private theorem width_readonly_frame (base : BitVec 64) (ops : List WidthOp) (s : ArmState)
    (hs : ∀ op ∈ ops, op ≠ .subSp ∧ op ≠ .save ∧ op ≠ .restore ∧ op ≠ .addSp) :
    WidthFrame s (widthBlock base ops s) := by
  induction ops generalizing s with
  | nil => exact WidthFrame.refl s
  | cons op ops ih =>
    obtain ⟨hsub, hsave, hrestore, hadd⟩ := hs op (List.mem_cons_self)
    exact (widthOp_readonly_frame base op s hsub hsave hrestore hadd).trans
      (ih _ (fun op ho => hs op (List.mem_cons_of_mem _ ho)))

private theorem width_spill_mem_w (s : ArmState) (f : StateField) (v : state_value f)
    (n : Nat) (addr : BitVec 64) (value : BitVec (n * 8)) :
    (write_mem_bytes n addr value (w f v s)).mem =
      (write_mem_bytes n addr value s).mem :=
  mem_write_mem_bytes_of_mem_eq (ArmState.mem_w_eq_mem f v s) n addr value

private theorem width_read_spill_w (s : ArmState) (f : StateField) (v : state_value f)
    (n m : Nat) (addr dst : BitVec 64) (value : BitVec (m * 8)) :
    read_mem_bytes n addr (write_mem_bytes m dst value (w f v s)) =
      read_mem_bytes n addr (write_mem_bytes m dst value s) :=
  (Memory.mem_eq_iff_read_mem_bytes_eq.mp (width_spill_mem_w s f v m dst value)) n addr

macro "width_simp" : tactic => `(tactic|
  simp (config := {decide := true, instances := true})
    [widthBlock, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
     Udivti3.compare, Udivti3.next, state_simp_rules, BitVec.add_assoc])

private def scanOps : List WidthOp :=
  [.subSp, .save, .index, .scale, .address, .load, .restore, .addSp,
   .remember, .decrement, .zero]

private def scanState (s : ArmState) (base word : BitVec 64) : ArmState :=
  w .PC (if word = 0#64 then base + 160#64 else base + 212#64)
    (w (.GPR 11#5) (r (.GPR 11#5) s - 1#64)
      (w (.GPR 10#5) (r (.GPR 11#5) s) (w (.GPR 12#5) word (widthSaved s))))

private theorem scanState_frame (s : ArmState) (base word : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) : WidthFrame s (scanState s base word) := by
  have hf := widthSaved_frame s hs
  constructor
  · simpa [scanState, state_simp_rules] using hf.program
  · simpa [scanState, state_simp_rules] using hf.error
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simpa (disch := simp_all) [scanState, state_simp_rules] using
      hf.registers reg (by simpa using hr)
  · intro reg; simpa [scanState, state_simp_rules] using hf.vectors reg
  · intro a ha; simpa [scanState, state_simp_rules] using hf.memory a ha

private theorem scan_read (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (n : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 168#64)
    (h8 : r (.GPR 8#5) s = pointer) (h11 : r (.GPR 11#5) s = BitVec.ofNat 64 n)
    (hn : n < words.length) (hs : WidthSource s pointer words)
    (hm : WidthWords s pointer words) :
    run 11 s = scanState s base (words[n]?.getD 0#64) := by
  have hsp := hs.1
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  have hshift : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8*n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have hload : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8*n)) (widthSaved s) =
      words[n]?.getD 0#64 := by
    have hl := (widthSaved_frame s hsp).words pointer words hs hm ⟨n, hn⟩
    simpa [List.getElem?_eq_getElem hn] using hl
  have hrestore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (widthSaved s) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  have hf : WidthFollows base scanOps s := by
    change r .PC s = _ at hp
    simp [scanOps, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
      state_simp_rules, hp, BitVec.add_assoc]
  rw [show 11 = scanOps.length by rfl, widthBlock_run base scanOps s hc he ha hf]
  simp only [widthSaved] at hload hrestore
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro f
    cases f with
    | GPR reg =>
      by_cases h31 : reg = 31#5
      · subst reg
        simp_all (config := {decide := true, instances := true})
          [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved,
           state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
      · by_cases h9 : reg = 9#5
        · subst reg
          simp_all (config := {decide := true, instances := true})
            [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved,
             state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
        · by_cases h11reg : reg = 11#5 <;> by_cases h10reg : reg = 10#5 <;>
            by_cases h12reg : reg = 12#5 <;> (try subst reg) <;>
            simp_all (config := {decide := true, instances := true})
              [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved,
               state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
    | SFP reg =>
      simp [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved, state_simp_rules]
    | PC =>
      simp_all (config := {decide := true, instances := true})
        [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved,
         state_simp_rules, width_read_spill_w, BitVec.sub_add_cancel]
    | FLAG flag =>
      simp [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved, state_simp_rules]
    | ERR =>
      simp [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved, state_simp_rules]
  · simp [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved, state_simp_rules]
  · intro n addr
    simp [widthBlock, scanOps, WidthOp.effect, wp, wn, scanState, widthSaved,
      state_simp_rules, width_read_spill_w]

private def scanExit (base : BitVec 64) (count : Nat) : BitVec 64 :=
  if count = 0 then base + 3724#64 else
    if count ≤ 2 then base + 3728#64 else base + 4544#64

private theorem width_significant_succ (words : List (BitVec 64)) (n : Nat) :
    significantCount words (n + 1) =
      if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl

/-- The actual descending scan, with arbitrary redundant high zeros. Each
recursive descent consumes a stored limb and performs/restores its scratch save. -/
private theorem width_scan (base pointer : BitVec 64) (words : List (BitVec 64)) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 160#64 →
    r (.GPR 8#5) s = pointer →
    r (.GPR 11#5) s = BitVec.ofNat 64 n - 1#64 →
    WidthSource s pointer words → WidthWords s pointer words →
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = scanExit base (significantCount words n) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h11 hs hm
    let t := widthBlock base [.testCount, .endCount] s
    have hz : (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2.z = 1#1 := by
      apply (width_count_z _).mpr
      simp [h11]
    refine ⟨2, t, widthBlock_run base [.testCount, .endCount] s hc he ha ?_,
      width_readonly_frame base _ s (by decide), ?_, ?_, ?_⟩
    · change r .PC s = _ at hp
      simpa [WidthFollows, WidthOp.row, WidthOp.effect, wn, state_simp_rules,
        BitVec.add_assoc, hp]
    · simp [t, widthBlock, WidthOp.effect, wn, state_simp_rules]
    · simp [t, widthBlock, WidthOp.effect, wn, state_simp_rules]
    · simp [t, widthBlock, WidthOp.effect, wn, state_simp_rules, hz,
        scanExit, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h8 h11 hs hm
    have hlen : words.length < 2^64 := by have := hs.2.1; omega
    have h11' : r (.GPR 11#5) s = BitVec.ofNat 64 n := by rw [h11]; bv_omega
    have hz : (AddWithCarry (r (.GPR 11#5) s) 1#64 0#1).2.z ≠ 1#1 := by
      intro hz
      have hz' := (width_count_z (r (.GPR 11#5) s)).mp hz
      rw [h11'] at hz'
      bv_omega
    let u := widthBlock base [.testCount, .endCount] s
    have hu : run 2 s = u := by
      apply widthBlock_run base [.testCount, .endCount] s hc he ha
      change r .PC s = _ at hp
      simp [WidthFollows, WidthOp.row, WidthOp.effect, wn, state_simp_rules,
        BitVec.add_assoc, hp]
    have huf : WidthFrame s u := width_readonly_frame base _ s (by decide)
    have hup : read_pc u = base + 168#64 := by
      simp [u, widthBlock, WidthOp.effect, wn, state_simp_rules, hz]
    have hu8 : r (.GPR 8#5) u = pointer := by
      simpa [u, widthBlock, WidthOp.effect, wn, state_simp_rules] using h8
    have hu11 : r (.GPR 11#5) u = BitVec.ofNat 64 n := by
      simpa [u, widthBlock, WidthOp.effect, wn, state_simp_rules] using h11'
    have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := by
      simp [u, widthBlock, WidthOp.effect, wn, state_simp_rules]
    let v := scanState u base (words[n]?.getD 0#64)
    have hv : run 11 u = v :=
      scan_read u base pointer words n
        (by simpa only [CodeAt, huf.program] using hc)
        (huf.error.trans he) (huf.aligned ha) hup hu8 hu11 (by omega)
        (huf.source _ _ hs) (huf.words _ _ hs hm)
    have husp : r (.GPR 31#5) u = r (.GPR 31#5) s := huf.sp
    have hss : 16 ≤ (r (.GPR 31#5) s).toNat := hs.1
    have hvf : WidthFrame s v := huf.trans (scanState_frame u base _ (by simpa only [husp] using hss))
    have hv8 : r (.GPR 8#5) v = pointer := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu8
    have hv9 : r (.GPR 9#5) v = r (.GPR 9#5) s := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu9
    have hv10 : r (.GPR 10#5) v = BitVec.ofNat 64 n := by
      simpa [v, scanState, widthSaved, state_simp_rules] using hu11
    have hv11 : r (.GPR 11#5) v = BitVec.ofNat 64 n - 1#64 := by
      simp [v, scanState, widthSaved, state_simp_rules, hu11]
    have hvs : run 13 s = v := by
      rw [show 13 = 2 + 11 by decide, run_plus, hu, hv]
    by_cases hw : words[n]?.getD 0#64 = 0#64
    · have hvp : read_pc v = base + 160#64 := by simp [v, scanState, state_simp_rules, hw]
      rcases ih v (by omega)
        (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he)
        (hvf.aligned ha) hvp hv8 hv11
        (hvf.source _ _ hs) (hvf.words _ _ hs hm) with
        ⟨fuel, t, ht, htf, ht8, ht9, htp⟩
      refine ⟨13 + fuel, t, ?_, hvf.trans htf, ?_, ht9.trans hv9, ?_⟩
      · rw [run_plus, hvs, ht]
      · exact ht8.trans (hv8.trans h8.symm)
      · simpa only [width_significant_succ, hw, ↓reduceIte] using htp
    · have hvp : read_pc v = base + 212#64 := by simp [v, scanState, state_simp_rules, hw]
      let ops : List WidthOp :=
        if n + 1 ≤ 2 then [.increment, .compareThree, .belowThree]
        else [.increment, .compareThree, .belowThree, .reject]
      let t := widthBlock base ops v
      have hcount : (BitVec.ofNat 64 n + 1#64).toNat = n + 1 := by bv_omega
      have hcarry : (AddWithCarry (BitVec.ofNat 64 n + 1#64) (~~~3#64) 1#1).2.c = 1#1 ↔
          3 ≤ n + 1 := by rw [Udivti3.cmp_carry, hcount]; rfl
      simp only [show (~~~3#64) = 18446744073709551612#64 by decide] at hcarry
      have ht : run ops.length v = t := by
        apply widthBlock_run base ops v
          (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he) (hvf.aligned ha)
        change r .PC v = _ at hvp
        by_cases hfew : n + 1 ≤ 2
        · simp [ops, hfew, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
            Udivti3.compare, Udivti3.next, state_simp_rules, hvp, hv10,
            BitVec.add_assoc]
        · have hc3 : 3 ≤ n + 1 := by omega
          simp [ops, hfew, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
            Udivti3.compare, Udivti3.next, state_simp_rules, hvp, hv10,
            BitVec.add_assoc, hcarry.mpr hc3]
      have htf : WidthFrame v t := width_readonly_frame base ops v (by
        dsimp only [ops]; split <;> decide)
      refine ⟨13 + ops.length, t, ?_, hvf.trans htf, ?_, ?_, ?_⟩
      · rw [run_plus, hvs, ht]
      · have heq : r (.GPR 8#5) t = r (.GPR 8#5) v := by
          unfold t ops; split <;> width_simp
        exact heq.trans (hv8.trans h8.symm)
      · have heq : r (.GPR 9#5) t = r (.GPR 9#5) v := by
          unfold t ops; split <;> width_simp
        exact heq.trans hv9
      · simp only [width_significant_succ, hw, ↓reduceIte, scanExit, Nat.succ_ne_zero]
        by_cases hfew : n + 1 ≤ 2
        · have hc3 : ¬ 3 ≤ n + 1 := by omega
          have hnc : (AddWithCarry (BitVec.ofNat 64 n + 1#64) 18446744073709551612#64 1#1).2.c ≠ 1#1 :=
            fun h => hc3 (hcarry.mp h)
          simp [t, ops, hfew, widthBlock, WidthOp.effect, wp, wn,
            Udivti3.compare, Udivti3.next, state_simp_rules, hv10, hnc]
        · simp [t, ops, hfew, widthBlock, WidthOp.effect, state_simp_rules]

private theorem width_low (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = base + 3728#64)
    (h8 : r (.GPR 8#5) s = pointer)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (hlen : words.length < 2^64) (hne : words ≠ [])
    (hm : WidthWords s pointer words) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = base + 4308#64 ∧
      r (.GPR 10#5) t = words[0]?.getD 0#64 ∧ r (.GPR 11#5) t = words[1]?.getD 0#64 := by
  have hpos : 0 < words.length := by cases words <;> simp_all
  have hl : read_mem_bytes 8 pointer s = words[0]?.getD 0#64 := by
    simpa [List.getElem?_eq_getElem hpos] using hm ⟨0, hpos⟩
  have hcount : (BitVec.ofNat 64 words.length).toNat = words.length := Nat.mod_eq_of_lt hlen
  have hcarry : (AddWithCarry (BitVec.ofNat 64 words.length) (~~~2#64) 1#1).2.c = 1#1 ↔
      2 ≤ words.length := by rw [Udivti3.cmp_carry, hcount]; rfl
  simp only [show (~~~2#64) = 18446744073709551613#64 by decide] at hcarry
  let ops : List WidthOp := if words.length < 2 then
    [.low, .compareTwo, .belowTwo, .oneHigh, .onePair] else
    [.low, .compareTwo, .belowTwo, .high, .pair]
  let t := widthBlock base ops s
  have ht : run ops.length s = t := by
    apply widthBlock_run base ops s hc he ha
    change r .PC s = _ at hp
    by_cases htwo : words.length < 2
    · have hnc : (AddWithCarry (BitVec.ofNat 64 words.length) 18446744073709551613#64 1#1).2.c ≠ 1#1 :=
        fun h => (by omega : ¬ 2 ≤ words.length) (hcarry.mp h)
      simp [ops, htwo, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
        Udivti3.compare, Udivti3.next, state_simp_rules, hp, h8, h9, hnc, BitVec.add_assoc]
    · have hc2 := hcarry.mpr (by omega : 2 ≤ words.length)
      simp [ops, htwo, WidthFollows, WidthOp.row, WidthOp.effect, wp, wn,
        Udivti3.compare, Udivti3.next, state_simp_rules, hp, h8, h9, hc2, BitVec.add_assoc]
  refine ⟨ops.length, t, ht, width_readonly_frame base ops s ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [ops]; split <;> decide
  · unfold t ops; split <;> width_simp
  · unfold t ops; split <;> width_simp
  · unfold t ops; split <;> width_simp
  · unfold t ops; split <;>
      simpa [widthBlock, WidthOp.effect, wp, wn, Udivti3.compare, Udivti3.next,
        state_simp_rules, h8] using hl
  · by_cases htwo : words.length < 2
    · have hz : words[1]?.getD 0#64 = 0 := by
        rw [List.getElem?_eq_none (by omega)]
        rfl
      simp [t, ops, htwo, widthBlock, WidthOp.effect, wp, wn,
        Udivti3.compare, Udivti3.next, state_simp_rules, hz]
    · have hh : read_mem_bytes 8 (pointer + 8#64) s = words[1]?.getD 0#64 := by
        simpa [List.getElem?_eq_getElem (by omega : 1 < words.length)] using hm ⟨1, by omega⟩
      simpa [t, ops, htwo, widthBlock, WidthOp.effect, wp, wn, Udivti3.compare,
        Udivti3.next, state_simp_rules, h8] using hh

private theorem width_prepare (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (hc : CodeAt s base) (he : read_err s = .None)
    (ha : CheckSPAlignment s) (hp : read_pc s = scanExit base (sigWords words))
    (h8 : r (.GPR 8#5) s = pointer)
    (h9 : r (.GPR 9#5) s = BitVec.ofNat 64 words.length)
    (hlen : words.length < 2^64) (hfew : sigWords words ≤ 2)
    (hm : WidthWords s pointer words) :
    ∃ fuel t, run fuel s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = base + 4308#64 ∧
      r (.GPR 10#5) t = words[0]?.getD 0#64 ∧ r (.GPR 11#5) t = words[1]?.getD 0#64 := by
  by_cases hz : sigWords words = 0
  · have hp' : read_pc s = base + 3724#64 := by simpa [scanExit, hz] using hp
    by_cases hn : words = []
    · subst words
      let t := widthBlock base [.empty, .emptyHigh, .emptyLow] s
      refine ⟨3, t, widthBlock_run base [.empty, .emptyHigh, .emptyLow] s hc he ha ?_,
        width_readonly_frame base [.empty, .emptyHigh, .emptyLow] s (by decide), ?_, ?_, ?_, ?_, ?_⟩
      · change r .PC s = _ at hp'
        simp [WidthFollows, WidthOp.row, WidthOp.effect, wp, wn, state_simp_rules,
          hp', h9, BitVec.add_assoc]
      all_goals simp [t, widthBlock, WidthOp.effect, wp, wn, state_simp_rules,
        h9, BitVec.add_assoc]
    · have hn9 : r (.GPR 9#5) s ≠ 0#64 := by
        rw [h9]
        have hpos : 0 < words.length := by cases words <;> simp_all
        bv_omega
      let u := WidthOp.empty.effect base s
      have hu : run 1 s = u := width_step s base .empty hc hp' he ha
      have huf : WidthFrame s u := width_pc_frame s _
      have hu8 : r (.GPR 8#5) u = r (.GPR 8#5) s := by simp [u, WidthOp.effect, state_simp_rules]
      have hu9 : r (.GPR 9#5) u = r (.GPR 9#5) s := by simp [u, WidthOp.effect, state_simp_rules]
      rcases width_low u base pointer words
        (by simpa only [CodeAt, huf.program] using hc) (huf.error.trans he) (huf.aligned ha)
        (by simp [u, WidthOp.effect, state_simp_rules, hn9])
        (hu8.trans h8) (hu9.trans h9) hlen hn
        (by simpa [WidthWords, u, WidthOp.effect, state_simp_rules] using hm) with
        ⟨fuel, t, ht, htf, ht8, ht9, htp, ht10, ht11⟩
      exact ⟨1 + fuel, t, by rw [run_plus, hu, ht], huf.trans htf,
        ht8.trans hu8, ht9.trans hu9, htp, ht10, ht11⟩
  · have hn : words ≠ [] := by intro h; subst words; simp [sigWords, significantCount] at hz
    exact width_low s base pointer words hc he ha
      (by simpa [scanExit, hz, hfew] using hp) h8 h9 hlen hn hm

private theorem width_pair (s : ArmState) (base : BitVec 64)
    (words : List (BitVec 64)) (hc : CodeAt s base) (he : read_err s = .None)
    (hp : read_pc s = base + 4308#64) (hfew : sigWords words ≤ 2)
    (h10 : r (.GPR 10#5) s = words[0]?.getD 0#64)
    (h11 : r (.GPR 11#5) s = words[1]?.getD 0#64) :
    ∃ t, run 3 s = t ∧ WidthFrame s t ∧
      r (.GPR 8#5) t = r (.GPR 8#5) s ∧ r (.GPR 9#5) t = r (.GPR 9#5) s ∧
      read_pc t = if value words = (r (.GPR 3#5) s).toNat then base + 4320#64 else base + 4544#64 := by
  let t := w .PC
    (if r (.GPR 10#5) s = r (.GPR 3#5) s ∧ r (.GPR 11#5) s = 0#64
     then base + 4320#64 else base + 4544#64) (widthJoined (widthXored s))
  refine ⟨t, width_comparison s base hc hp he, ?_, ?_, ?_, ?_⟩
  · constructor
    · simp [t, widthJoined, widthXored, state_simp_rules]
    · simp [t, widthJoined, widthXored, state_simp_rules]
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all) [t, widthJoined, widthXored, state_simp_rules]
    · intro reg; simp [t, widthJoined, widthXored, state_simp_rules]
    · intro a ha; simp [t, widthJoined, widthXored, state_simp_rules]
  · simp [t, widthJoined, widthXored, state_simp_rules]
  · simp [t, widthJoined, widthXored, state_simp_rules]
  · have hpair : (words[0]?.getD 0#64 = r (.GPR 3#5) s ∧ words[1]?.getD 0#64 = 0#64) ↔
          value words = (r (.GPR 3#5) s).toNat := width_pair_words words (r (.GPR 3#5) s) hfew
    simp only [t, state_simp_rules, h10, h11, hpair]

/-- Exact integration boundary: the error path still holds the original header
words in x8/x9; all outcomes preserve the complete non-scratch register file.
The original SP is unchanged, aligned, and memory outside [SP-16,SP) is framed. -/
def WidthPost (s : ArmState) (base : BitVec 64) (expectedWidth : Nat)
    (t : ArmState) : Prop :=
  WidthFrame s t ∧ CheckSPAlignment t ∧
  r (.GPR 8#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
  r (.GPR 9#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s ∧
  read_pc t = if expectedWidth = (r (.GPR 3#5) s).toNat then base + 4320#64 else base + 4544#64

private theorem widthLoaded_frame (s : ArmState) : WidthFrame s (widthLoaded s) := by
  constructor
  · simp [widthLoaded, state_simp_rules]
  · simp [widthLoaded, state_simp_rules]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [widthLoaded, state_simp_rules]
  · intro reg; simp [widthLoaded, state_simp_rules]
  · intro a ha; simp [widthLoaded, state_simp_rules]

theorem width_small_runs (s : ArmState) (base : BitVec 64) (hc : CodeAt s base)
    (hp : read_pc s = base + 148#64) (he : read_err s = .None)
    (ha : CheckSPAlignment s)
    (hsmall : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64) :
    WidthPost s base (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s).toNat (run 8 s) := by
  rw [small_descriptor s base hc hp he hsmall]
  have hf : WidthFrame s
      (w .PC
        (if read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = r (.GPR 3#5) s then base + 4320#64 else base + 4544#64)
        (widthJoined (widthXored (smallWidthPrepared (w .PC (base + 3368#64) (widthLoaded s)) base)))) := by
    constructor
    · simp [widthJoined, widthXored, smallWidthPrepared, widthLoaded, state_simp_rules]
    · simp [widthJoined, widthXored, smallWidthPrepared, widthLoaded, state_simp_rules]
    · intro reg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (disch := simp_all)
        [widthJoined, widthXored, smallWidthPrepared, widthLoaded, state_simp_rules]
    · intro reg
      simp [widthJoined, widthXored, smallWidthPrepared, widthLoaded, state_simp_rules]
    · intro a h
      simp [widthJoined, widthXored, smallWidthPrepared, widthLoaded, state_simp_rules]
  refine ⟨hf, hf.aligned ha, ?_, ?_, ?_⟩
  all_goals simp [widthJoined, widthXored, smallWidthPrepared, widthLoaded,
    state_simp_rules, BitVec.toNat_inj]

theorem width_large_runs (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (hc : CodeAt s base)
    (hp : read_pc s = base + 148#64) (he : read_err s = .None)
    (ha : CheckSPAlignment s)
    (hptr : pointer ≠ 0#64)
    (h8 : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = pointer)
    (h9 : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s = BitVec.ofNat 64 words.length)
    (hs : WidthSource s pointer words) (hm : WidthWords s pointer words) :
    WidthRuns s (WidthPost s base (value words)) := by
  have hlen : words.length < 2^64 := by have := hs.2.1; omega
  let u := w .PC (base + 156#64) (widthLoaded s)
  have hu : run 2 s = u := by
    have hb := width_branch s base hc hp he
    change run 2 s = w .PC
      (if read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64 then base + 3368#64 else base + 156#64)
      (widthLoaded s) at hb
    simpa only [h8, hptr, ↓reduceIte] using hb
  have huf : WidthFrame s u := (widthLoaded_frame s).trans (width_pc_frame _ _)
  have hu8 : r (.GPR 8#5) u = pointer := by simpa [u, widthLoaded, state_simp_rules] using h8
  have hu9 : r (.GPR 9#5) u = BitVec.ofNat 64 words.length := by
    simpa [u, widthLoaded, state_simp_rules] using h9
  let v := WidthOp.subCount.effect base u
  have hv : run 1 u = v := width_step u base .subCount
    (by simpa only [CodeAt, huf.program] using hc)
    (by simp [u, WidthOp.row, state_simp_rules]) (huf.error.trans he) (huf.aligned ha)
  have hvf : WidthFrame s v := huf.trans (width_put_frame u 11 _ (by decide))
  have hv8 : r (.GPR 8#5) v = pointer := by simpa [v, WidthOp.effect, wp, wn, state_simp_rules] using hu8
  have hv9 : r (.GPR 9#5) v = BitVec.ofNat 64 words.length := by
    simpa [v, WidthOp.effect, wp, wn, state_simp_rules] using hu9
  have hvs : run 3 s = v := by rw [show 3 = 2 + 1 by decide, run_plus, hu, hv]
  rcases width_scan base pointer words words.length v (Nat.le_refl _)
    (by simpa only [CodeAt, hvf.program] using hc) (hvf.error.trans he) (hvf.aligned ha)
    (by simp [v, WidthOp.effect, wp, wn, u, state_simp_rules, BitVec.add_assoc])
    hv8 (by simp [v, WidthOp.effect, wp, wn, state_simp_rules, hu9])
    (hvf.source _ _ hs) (hvf.words _ _ hs hm) with
    ⟨fuel, t, ht, htf, ht8, ht9, htp⟩
  have hsf : WidthFrame s t := hvf.trans htf
  have hs8 : r (.GPR 8#5) t = pointer := ht8.trans hv8
  have hs9 : r (.GPR 9#5) t = BitVec.ofNat 64 words.length := ht9.trans hv9
  apply WidthRuns.prefix 3 hvs
  apply WidthRuns.prefix fuel ht
  by_cases hfew : sigWords words ≤ 2
  · rcases width_prepare t base pointer words
      (by simpa only [CodeAt, hsf.program] using hc) (hsf.error.trans he) (hsf.aligned ha)
      htp hs8 hs9 hlen hfew (hsf.words _ _ hs hm) with
      ⟨count, q, hq, hqf, hq8, hq9, hqp, hq10, hq11⟩
    have hqsf := hsf.trans hqf
    rcases width_pair q base words
      (by simpa only [CodeAt, hqsf.program] using hc) (hqsf.error.trans he)
      hqp hfew hq10 hq11 with ⟨r, hr, hrf, hr8, hr9, hrp⟩
    have hfinal := hqsf.trans hrf
    apply WidthRuns.prefix count hq
    apply WidthRuns.prefix 3 hr
    apply WidthRuns.done
    refine ⟨hfinal, hfinal.aligned ha, hr8.trans (hq8.trans (hs8.trans h8.symm)),
      hr9.trans (hq9.trans (hs9.trans h9.symm)), ?_⟩
    simpa only [hqsf.registers 3#5 (by decide)] using hrp
  · have hmany : 2 < sigWords words := by omega
    have hne := width_many_ne words (r (.GPR 3#5) s) hmany
    have hnz : sigWords words ≠ 0 := by omega
    apply WidthRuns.done
    refine ⟨hsf, hsf.aligned ha, hs8.trans h8.symm, hs9.trans h9.symm, ?_⟩
    change read_pc t = scanExit base (sigWords words) at htp
    simpa only [scanExit, hfew, hnz, hne, ↓reduceIte] using htp

/-- Source/scratch separation is conditional on a Large header. For Small there
is no borrowed slice and the prefix performs no scratch writes at all. -/
def WidthScratchSeparated (s : ArmState) : Prop :=
  16 ≤ (r (.GPR 31#5) s).toNat ∧
  let pointer := read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s
  let count := read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s
  pointer ≠ 0#64 →
    pointer.toNat + 8 * count.toNat ≤ (r (.GPR 31#5) s).toNat - 16 ∨
      (r (.GPR 31#5) s).toNat ≤ pointer.toNat

/-- COMPLETE actual descriptor-width prefix, from linked PC148 to PC4320 on
mathematical equality and PC4544 otherwise. This includes Large [], all-zero
limbs, noncanonical redundant high zeros, early rejection of three significant
words, and the one/two-word comparison. The hypotheses describe only initial
physical representation, address bounds, code and stack safety: none assumes
execution, a significant-count result, or the desired numerical comparison. -/
theorem width_runs (s : ArmState) (base : BitVec 64) (expectedWidth : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 148#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (_hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hs : WidthScratchSeparated s)
    (hwidth : SszNative.NatMemory.At (widthLoad s)
      ((r (.GPR 1#5) s).toNat + 8) expectedWidth) :
    ∃ fuel, WidthPost s base expectedWidth (run fuel s) := by
  rcases hwidth with ⟨⟨hzero, hvalue⟩, hbound⟩ |
    ⟨pointer, words, hlarge, hvalue⟩
  · have hz : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, BitVec.ofNat_add] using hzero
    have hv : (read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s).toNat = expectedWidth := by
      simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc] using hvalue
    exact ⟨8, by simpa only [hv] using width_small_runs s base hc hp he ha hz⟩
  · rcases hlarge with ⟨hpositive, hbound, _halign, hspace, hptr, hcount, hwords⟩
    let p := BitVec.ofNat 64 pointer
    have hpn : p.toNat = pointer := Nat.mod_eq_of_lt hbound
    have hlen : words.length < 2^64 := by omega
    have hn : (BitVec.ofNat 64 words.length).toNat = words.length := Nat.mod_eq_of_lt hlen
    have hp0 : p ≠ 0#64 := by intro h; have := congrArg BitVec.toNat h; simp [hpn] at this; omega
    have h8 : read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s = p := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, BitVec.ofNat_add, hpn] using hptr
    have h9 : read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s =
        BitVec.ofNat 64 words.length := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, Nat.add_assoc, BitVec.ofNat_add, BitVec.add_assoc, hn] using hcount
    have hsource : WidthSource s p words := by
      refine ⟨hs.1, by simpa only [hpn] using hspace, ?_⟩
      change p.toNat + 8 * words.length ≤ (r (.GPR 31#5) s).toNat - 16 ∨
        (r (.GPR 31#5) s).toNat ≤ p.toNat
      have hsep := hs.2
      dsimp only at hsep
      simpa only [h8, h9, hn] using hsep (by simpa only [h8] using hp0)
    have hm : WidthWords s p words := by
      intro i
      apply BitVec.eq_of_toNat_eq
      have hi := hwords i
      simpa [SszNative.NatMemory.wordsAt, widthLoad, p, BitVec.ofNat_add] using hi
    simpa only [WidthRuns, hvalue] using width_large_runs s base p words hc hp he ha hp0 h8 h9 hsource hm

/-- Composition form: either continuation starts at its actual linked PC with
the frame and original descriptor header available. -/
theorem width_cps (s : ArmState) (base : BitVec 64) (expectedWidth : Nat)
    (hc : CodeAt s base) (hp : read_pc s = base + 148#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hs : WidthScratchSeparated s)
    (hwidth : SszNative.NatMemory.At (widthLoad s)
      ((r (.GPR 1#5) s).toNat + 8) expectedWidth)
    (P : ArmState → Prop)
    (hk : ∀ t, WidthPost s base expectedWidth t → WidthRuns t P) :
    WidthRuns s P := by
  rcases width_runs s base expectedWidth hc hp he ha hheader hs hwidth with ⟨fuel, hf⟩
  exact WidthRuns.prefix fuel rfl (hk _ hf)

end SszArm.UintCodec
