import SszArm.DelimitedBlocks
import SszArm.DelimitedMemory

namespace SszArm.Delimited

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

structure ScanFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [2#5, 3#5, 8#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : t.mem = s.mem

theorem ScanFrame.trans {s t u : ArmState} (st : ScanFrame s t) (tu : ScanFrame t u) :
    ScanFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg), tu.memory.trans st.memory⟩

theorem ScanFrame.aligned {s t : ArmState} (frame : ScanFrame s t)
    (aligned : CheckSPAlignment s) : CheckSPAlignment t := by
  have sp := frame.registers 31#5 (by decide)
  simpa only [CheckSPAlignment, state_simp_rules, sp] using aligned

def ScanBytes (s : ArmState) : BitVec 64 → List (BitVec 8) → Prop
  | _, [] => True
  | pointer, byte :: bytes => read_mem_bytes 1 pointer s = byte ∧
      ScanBytes s (pointer + 1#64) bytes

theorem ScanFrame.bytes {s t : ArmState} (frame : ScanFrame s t)
    (pointer : BitVec 64) (bytes : List (BitVec 8)) (input : ScanBytes s pointer bytes) :
    ScanBytes t pointer bytes := by
  induction bytes generalizing pointer with
  | nil => trivial
  | cons byte bytes ih =>
    refine ⟨?_, ih _ input.2⟩
    rw [(Memory.mem_eq_iff_read_mem_bytes_eq.mp frame.memory) 1 pointer]
    exact input.1

def scanRoundOps : List Op := [.p184, .p172, .p176, .p180]

private theorem scan_round_frame (s : ArmState) (base : BitVec 64) :
    ScanFrame s (block base scanRoundOps s) := by
  constructor
  · exact block_program _ _ _
  · exact block_error _ _ _
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (disch := simp_all) [block, scanRoundOps, Op.effect, put, next, state_simp_rules]
  · intro reg
    simp [block, scanRoundOps, Op.effect, put, next, state_simp_rules]
  · simp [block, scanRoundOps, Op.effect, put, next, state_simp_rules]

private theorem scan_test_frame (s : ArmState) (base : BitVec 64) :
    ScanFrame s (Op.p184.effect base s) := by
  constructor
  · exact Op.program _ _ _
  · exact Op.error _ _ _
  · intro reg hr; simp [Op.effect, state_simp_rules]
  · intro reg; simp [Op.effect, state_simp_rules]
  · simp [Op.effect, state_simp_rules]

/-- The final-byte-zero path scans the original entire input. Empty remainder
selects NoDelimiter; the first nonzero byte selects TrailingZeros. All memory is
read-only, and no optional-limit or arena field is inspected. -/
theorem zero_scan (base : BitVec 64) (bytes : List (BitVec 8)) :
    ∀ s, CodeAt s base → read_err s = .None → CheckSPAlignment s →
      read_pc s = base + 184#64 →
      r (.GPR 3#5) s = BitVec.ofNat 64 bytes.length → bytes.length < 2^64 →
      ScanBytes s (r (.GPR 2#5) s) bytes →
      ∃ fuel t, run fuel s = t ∧ ScanFrame s t ∧
        read_pc t = if bytes.all (· == 0#8) then base + 188#64 else base + 616#64 := by
  induction bytes with
  | nil =>
    intro s hc he ha hp length bound input
    let t := Op.p184.effect base s
    refine ⟨1, t, ?_, scan_test_frame s base, ?_⟩
    · simpa only [run] using step s base .p184 hc (by simpa only [Op.row] using hp) he ha
    · simp [t, Op.effect, state_simp_rules, length]
  | cons byte bytes ih =>
    intro s hc he ha hp length bound input
    have nonzero : r (.GPR 3#5) s ≠ 0#64 := by
      rw [length]
      have size : 0 < (byte :: bytes).length := by simp
      bv_omega
    let u := block base scanRoundOps s
    have hu : run 4 s = u := by
      apply block_run base scanRoundOps s hc he ha
      have hpc : r .PC s = base + 184#64 := hp
      simp [scanRoundOps, Follows, Op.row, Op.effect, put, next,
        state_simp_rules, hpc, nonzero, BitVec.add_assoc]
    have frame : ScanFrame s u := scan_round_frame s base
    have pointer : r (.GPR 2#5) u = r (.GPR 2#5) s + 1#64 := by
      simp [u, block, scanRoundOps, Op.effect, put, next, state_simp_rules]
    have count : r (.GPR 3#5) u = BitVec.ofNat 64 bytes.length := by
      simp [u, block, scanRoundOps, Op.effect, put, next, state_simp_rules, length] <;>
        bv_omega
    have inputTail : ScanBytes u (r (.GPR 2#5) u) bytes := by
      rw [pointer]
      exact frame.bytes _ _ input.2
    have load : read_mem_bytes 1 (r (.GPR 2#5) s) s = byte := input.1
    have byteZero : byte.setWidth 32 = 0#32 ↔ byte = 0#8 := by bv_omega
    have pc : read_pc u = if byte = 0#8 then base + 184#64 else base + 616#64 := by
      simp [u, block, scanRoundOps, Op.effect, put, next, state_simp_rules, load, byteZero]
    by_cases zero : byte = 0#8
    · obtain ⟨fuel, t, ht, hf, hpc⟩ := ih u
        (by simpa only [CodeAt, frame.program] using hc) (frame.error.trans he)
        (frame.aligned ha) (by simpa only [zero, ↓reduceIte] using pc)
        count (by simp only [List.length_cons] at bound; omega) inputTail
      refine ⟨4 + fuel, t, ?_, frame.trans hf, ?_⟩
      · rw [run_plus, hu, ht]
      · simpa [zero] using hpc
    · refine ⟨4, u, hu, frame, ?_⟩
      simpa [zero] using pc

end SszArm.Delimited
