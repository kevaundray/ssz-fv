import SszArm.NatAddBlocks
import SszNatOperandNormalization

namespace SszArm.NatAdd.Normalize

open UintCodec SszNative.Limbs
open NatCompare (Words)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- The output normalization scan is read-only, even at its post-indexed load. -/
structure Frame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [8#5, 10#5, 12#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : t.mem = s.mem

theorem Frame.refl (s : ArmState) : Frame s s :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl, rfl⟩

theorem Frame.trans {s t u : ArmState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.program.trans h.program, k.error.trans h.error,
    fun reg hr => (k.registers reg hr).trans (h.registers reg hr),
    fun reg => (k.vectors reg).trans (h.vectors reg), k.memory.trans h.memory⟩

theorem Frame.code {s t : ArmState} (h : Frame s t) {base : BitVec 64}
    (hc : CodeAt s base) : CodeAt t base := by
  simpa only [CodeAt, h.program] using hc

theorem Frame.aligned {s t : ArmState} (h : Frame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  have sp := h.registers 31#5 (by decide)
  simpa only [CheckSPAlignment, state_simp_rules, sp] using ha

theorem Frame.words {s t : ArmState} (h : Frame s t)
    (pointer : BitVec 64) (words : List (BitVec 64)) (hm : Words s pointer words) :
    Words t pointer words := by
  intro i
  rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp h.memory]
  exact hm i

def scanOps : List Op := [.p2044, .p2048, .p2052, .p2056, .p2060, .p2064]

theorem scan_frame (base : BitVec 64) (ops : List Op) (s : ArmState)
    (allowed : ∀ op ∈ ops, op ∈ scanOps) : Frame s (block base ops s) := by
  induction ops generalizing s with
  | nil => exact Frame.refl s
  | cons op ops ih =>
    have hx := allowed op List.mem_cons_self
    have frame : Frame s (op.effect base s) := by
      cases op <;> simp_all only [scanOps, List.mem_cons, List.not_mem_nil,
        or_false, reduceCtorEq, false_or, or_self]
      all_goals
        constructor
        · simp [Op.effect, put, next, state_simp_rules]
        · simp [Op.effect, put, next, state_simp_rules]
        · intro reg hr
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]
        · intro reg; simp [Op.effect, put, next, state_simp_rules]
        · simp [Op.effect, put, next, state_simp_rules]
    exact frame.trans (ih _ (fun op hop => allowed op (List.mem_cons_of_mem _ hop)))

def round (s : ArmState) (base : BitVec 64) : ArmState :=
  block base [.p2052, .p2056, .p2060, .p2064] s

/-- +2060 reads at the old X10 and only then subtracts eight from X10. -/
theorem round_run (s : ArmState) (base pointer : BitVec 64)
    (words : List (BitVec 64)) (index : Nat)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 2052#64)
    (h8 : r (.GPR 8#5) s = BitVec.ofNat 64 (index + 2))
    (h10 : r (.GPR 10#5) s = pointer + BitVec.ofNat 64 (8 * index))
    (hi : index < words.length) (bound : words.length + 1 < 2^64)
    (hm : Words s pointer words) :
    run 4 s = round s base ∧ Frame s (round s base) ∧
      r (.GPR 8#5) (round s base) = BitVec.ofNat 64 (index + 1) ∧
      r (.GPR 10#5) (round s base) = pointer + BitVec.ofNat 64 (8 * index) - 8#64 ∧
      read_pc (round s base) =
        base + (if words[index]?.getD 0#64 = 0#64 then 2052#64 else 2068#64) := by
  have load : read_mem_bytes 8 (pointer + BitVec.ofNat 64 (8 * index)) s =
      words[index]?.getD 0#64 := by
    simpa [List.getElem?_eq_getElem hi] using hm ⟨index, hi⟩
  have dec : BitVec.ofNat 64 (index + 2) - 1#64 = BitVec.ofNat 64 (index + 1) := by bv_omega
  have nonzero : BitVec.ofNat 64 (index + 2) ≠ 1#64 := by bv_omega
  have hpc : r .PC s = base + 2052#64 := hp
  have follows : Follows base [.p2052, .p2056, .p2060, .p2064] s := by
    simp [Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, h8, nonzero, BitVec.add_assoc]
  refine ⟨block_run base _ s hc he ha follows, scan_frame base _ s (by decide), ?_, ?_, ?_⟩
  · simp [round, block, Op.effect, put, next, state_simp_rules, h8, dec]
  · simp [round, block, Op.effect, put, next, state_simp_rules, h10, BitVec.sub_eq_add_neg]
  · by_cases zero : words[index]?.getD 0#64 = 0#64 <;>
      simp [round, block, Op.effect, put, next, state_simp_rules, h10, load, zero]

/-- Complete backward normalization scan, retaining original noncanonical
physical words while computing their exact significant count. -/
theorem scan_run (base pointer : BitVec 64) (words : List (BitVec 64))
    (bound : words.length + 1 < 2^64) :
    ∀ n (s : ArmState), n ≤ words.length →
    CodeAt s base → read_err s = .None → CheckSPAlignment s →
    read_pc s = base + 2052#64 →
    r (.GPR 8#5) s = BitVec.ofNat 64 (n + 1) →
    r (.GPR 10#5) s = pointer + BitVec.ofNat 64 (8 * n) - 8#64 →
    Words s pointer words →
    ∃ fuel t, run fuel s = t ∧ Frame s t ∧
      r (.GPR 8#5) t = BitVec.ofNat 64 (significantCount words n) ∧
      read_pc t = base + (if significantCount words n = 0 then 2128#64 else 2068#64) := by
  intro n
  induction n with
  | zero =>
    intro s hn hc he ha hp h8 h10 hm
    let ops : List Op := [.p2052, .p2056]
    let t := block base ops s
    have hpc : r .PC s = base + 2052#64 := hp
    refine ⟨2, t, block_run base ops s hc he ha (by
      simp [ops, Follows, Op.row, Op.effect, put, next, state_simp_rules,
        hpc, h8, BitVec.add_assoc]), scan_frame base ops s (by decide), ?_, ?_⟩
    all_goals simp [t, ops, block, Op.effect, put, next, state_simp_rules, h8, significantCount]
  | succ n ih =>
    intro s hn hc he ha hp h8 h10 hm
    have h10' : r (.GPR 10#5) s = pointer + BitVec.ofNat 64 (8 * n) := by
      rw [h10]
      bv_omega
    obtain ⟨runRound, frame, next8, next10, nextPC⟩ :=
      round_run s base pointer words n hc he ha hp h8 h10' (by omega) bound hm
    let v := round s base
    change run 4 s = v at runRound
    change Frame s v at frame
    change r (.GPR 8#5) v = BitVec.ofNat 64 (n + 1) at next8
    change r (.GPR 10#5) v = pointer + BitVec.ofNat 64 (8 * n) - 8#64 at next10
    change read_pc v = base + (if words[n]?.getD 0#64 = 0#64 then 2052#64 else 2068#64) at nextPC
    have recurrence : significantCount words (n + 1) =
        if words[n]?.getD 0#64 = 0#64 then significantCount words n else n + 1 := rfl
    by_cases zero : words[n]?.getD 0#64 = 0#64
    · have vp : read_pc v = base + 2052#64 := by simpa only [zero, ↓reduceIte] using nextPC
      obtain ⟨fuel, t, runRest, restFrame, final8, finalPC⟩ := ih v (by omega)
        (frame.code hc) (frame.error.trans he) (frame.aligned ha) vp next8 next10
        (frame.words _ _ hm)
      refine ⟨4 + fuel, t, ?_, frame.trans restFrame, ?_, ?_⟩
      · rw [run_plus, runRound, runRest]
      · simpa only [recurrence, zero, ↓reduceIte] using final8
      · simpa only [recurrence, zero, ↓reduceIte] using finalPC
    · refine ⟨4, v, runRound, frame, ?_, ?_⟩
      · simpa only [recurrence, zero, ↓reduceIte] using next8
      · simpa [recurrence, zero] using nextPC

end SszArm.NatAdd.Normalize
