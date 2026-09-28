import SszArm.NatMulReserveClassify
import SszArm.NatMulCalls
import SszArm.NatCompareMemory
import SszArm.DelimitedMemory

namespace SszArm.NatMul

def reserveCommitOps : List Op :=
  [.p536, .p540, .p544, .p548, .p552, .p556, .p560, .p564, .p568, .p572]

def reserveCursorMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 5#5) s + 16#64) (r (.GPR 12#5) s) s

/-- The actual pre-call register arrangement, including the original operands. -/
structure ReserveCommitState (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 576#64
  pointer : r (.GPR 20#5) t = r (.GPR 10#5) s + r (.GPR 11#5) s
  result : r (.GPR 24#5) t = r (.GPR 0#5) s
  left : r (.GPR 26#5) t = r (.GPR 1#5) s
  right : r (.GPR 27#5) t = r (.GPR 3#5) s
  payload : r (.GPR 28#5) t = r (.GPR 8#5) s
  rowEnd : r (.GPR 23#5) t = r (.GPR 21#5) s + r (.GPR 9#5) s
  rowNext : r (.GPR 25#5) t = r (.GPR 9#5) s + 1#64
  destination : r (.GPR 0#5) t = r (.GPR 20#5) t
  zero : r (.GPR 1#5) t = 0#64
  registers : ∀ reg : BitVec 5, reg ∉ [0#5, 1#5, 20#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  memory : t.mem = (reserveCursorMemory s).mem
  program : t.program = s.program
  error : read_err t = read_err s

private theorem reserve_commit_registers_block (base : BitVec 64) (ops : List Op)
    (allowed : ∀ op ∈ ops, op ∈ reserveCommitOps) (s : ArmState) (reg : BitVec 5)
    (hr : reg ∉ [0#5, 1#5, 20#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5]) :
    r (.GPR reg) (block base ops s) = r (.GPR reg) s := by
  apply reserve_block_preserves (r (.GPR reg)) base ops
  intro op member t
  have hop := allowed op member
  simp only [reserveCommitOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_read_mem (base : BitVec 64) (ops : List Op)
    (allowed : ∀ op ∈ ops, op ∈ [.p536, .p540, .p544, .p548, .p552, .p556, .p560, .p568, .p572])
    (s : ArmState) : (block base ops s).mem = s.mem := by
  apply reserve_block_preserves (fun t => t.mem) base ops
  intro op member t
  have hop := allowed op member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_mem (s : ArmState) (base : BitVec 64) :
    (block base reserveCommitOps s).mem = (reserveCursorMemory s).mem := by
  let before : List Op := [.p536, .p540, .p544, .p548, .p552, .p556, .p560]
  have splitBlock : block base reserveCommitOps s =
      block base [.p568, .p572] (Op.p564.effect base (block base before s)) := by
    simp only [reserveCommitOps, before, block, List.foldl_cons, List.foldl_nil]
  have preserved : (block base before s).mem = s.mem :=
    reserve_commit_read_mem base before (by simp [before]) s
  have reg5 : r (.GPR 5#5) (block base before s) = r (.GPR 5#5) s :=
    reserve_commit_registers_block base before (by simp [before, reserveCommitOps]) s 5#5 (by decide)
  have reg12 : r (.GPR 12#5) (block base before s) = r (.GPR 12#5) s :=
    reserve_commit_registers_block base before (by simp [before, reserveCommitOps]) s 12#5 (by decide)
  have stored (t : ArmState) : (Op.p564.effect base t).mem =
      (write_mem_bytes 8 (r (.GPR 5#5) t + 16#64) (r (.GPR 12#5) t) t).mem := by
    simp [Op.effect, next, state_simp_rules]
  rw [splitBlock, reserve_commit_read_mem base _ (by simp), stored, reg5, reg12]
  exact mem_write_mem_bytes_of_mem_eq preserved _ _ _

private theorem reserve_commit_pc (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 536#64) :
    read_pc (block base reserveCommitOps s) = base + 576#64 := by
  have hpc : r .PC s = base + 536#64 := hp
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

private theorem reserve_commit_pointer (s : ArmState) (base : BitVec 64) :
    r (.GPR 20#5) (block base reserveCommitOps s) = r (.GPR 10#5) s + r (.GPR 11#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_result (s : ArmState) (base : BitVec 64) :
    r (.GPR 24#5) (block base reserveCommitOps s) = r (.GPR 0#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_left (s : ArmState) (base : BitVec 64) :
    r (.GPR 26#5) (block base reserveCommitOps s) = r (.GPR 1#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_right (s : ArmState) (base : BitVec 64) :
    r (.GPR 27#5) (block base reserveCommitOps s) = r (.GPR 3#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_payload (s : ArmState) (base : BitVec 64) :
    r (.GPR 28#5) (block base reserveCommitOps s) = r (.GPR 8#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_row_end (s : ArmState) (base : BitVec 64) :
    r (.GPR 23#5) (block base reserveCommitOps s) = r (.GPR 21#5) s + r (.GPR 9#5) s := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_row_next (s : ArmState) (base : BitVec 64) :
    r (.GPR 25#5) (block base reserveCommitOps s) = r (.GPR 9#5) s + 1#64 := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_destination (s : ArmState) (base : BitVec 64) :
    r (.GPR 0#5) (block base reserveCommitOps s) = r (.GPR 20#5) (block base reserveCommitOps s) := by
  rw [reserve_commit_pointer]
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

private theorem reserve_commit_zero (s : ArmState) (base : BitVec 64) :
    r (.GPR 1#5) (block base reserveCommitOps s) = 0#64 := by
  simp [reserveCommitOps, block, Op.effect, put, next, state_simp_rules]

theorem reserve_commit_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 536#64) :
    ReserveCommitState s (block base reserveCommitOps s) base :=
  {
    pc := reserve_commit_pc s base hp
    pointer := reserve_commit_pointer s base
    result := reserve_commit_result s base
    left := reserve_commit_left s base
    right := reserve_commit_right s base
    payload := reserve_commit_payload s base
    rowEnd := reserve_commit_row_end s base
    rowNext := reserve_commit_row_next s base
    destination := reserve_commit_destination s base
    zero := reserve_commit_zero s base
    registers := reserve_commit_registers_block base reserveCommitOps (fun _ h => h) s
    vectors := fun reg => reserve_block_preserves (r (.SFP reg)) base reserveCommitOps
      (fun op _ t => op.sfp base t reg) s
    memory := reserve_commit_mem s base
    program := block_program _ _ _
    error := block_error _ _ _
  }

theorem reserve_commit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 536#64) :
    run 10 s = block base reserveCommitOps s := by
  apply block_run base reserveCommitOps s hc he ha
  have hpc : r .PC s = base + 536#64 := hp
  simp [reserveCommitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem reserve_commit_memory (s : ArmState) (base : BitVec 64)
    (physical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64)
    (hp : read_pc s = base + 536#64) :
    let t := block base reserveCommitOps s
    Delimited.MemoryFrame [((r (.GPR 5#5) s + 16#64).toNat, 8)] s t ∧
      read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) t = r (.GPR 12#5) s := by
  dsimp only
  have hm := (reserve_commit_effect s base hp).memory
  constructor
  · intro a outside
    rw [hm]
    exact BoolCodec.write_mem_bytes_frame _ _ _ _ a physical
      (outside ((r (.GPR 5#5) s + 16#64).toNat, 8) (by simp))
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ physical

/-- Exact helper-visible arrangement and image at the returned PC. In particular,
the zero destination is a consequence of the actual runtime helper execution. -/
structure ReserveZeroState (s t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 580#64
  error : read_err t = .None
  program : t.program = s.program
  pointer : r (.GPR 20#5) t = r (.GPR 10#5) s + r (.GPR 11#5) s
  result : r (.GPR 24#5) t = r (.GPR 0#5) s
  left : r (.GPR 26#5) t = r (.GPR 1#5) s
  right : r (.GPR 27#5) t = r (.GPR 3#5) s
  payload : r (.GPR 28#5) t = r (.GPR 8#5) s
  rowEnd : r (.GPR 23#5) t = r (.GPR 21#5) s + r (.GPR 9#5) s
  rowNext : r (.GPR 25#5) t = r (.GPR 9#5) s + 1#64
  registers : ∀ reg : BitVec 5,
    reg ∉ [0#5, 1#5, 2#5, 3#5, 20#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5, 30#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, reg ≠ 0#5 → r (.SFP reg) t = r (.SFP reg) s
  memory : ∀ a, t.mem a = Memset.image (reserveCursorMemory s).mem
    (r (.GPR 10#5) s + r (.GPR 11#5) s) 0#8 (r (.GPR 2#5) s).toNat a

theorem reserve_commit_zero_runs (s : ArmState) (base : BitVec 64)
    (hc : JointCodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 536#64)
    (physical : (r (.GPR 10#5) s + r (.GPR 11#5) s).toNat + (r (.GPR 2#5) s).toNat ≤ 2^64) :
    ∃ fuel t, run fuel s = t ∧ ReserveZeroState s t base := by
  let u := block base reserveCommitOps s
  have runU := reserve_commit_run s base hc.body he ha hp
  have effect := reserve_commit_effect s base hp
  have r2 := effect.registers 2#5 (by decide)
  obtain ⟨t, runT, error, pc, program, preserved, memory⟩ :=
    memset_call_run u base (hc.transport effect.program) (effect.error.trans he) effect.pc
      (by rw [effect.destination, effect.pointer, r2]; exact physical)
  have reg (i : BitVec 5) (h2 : i ≠ 2#5) (h3 : i ≠ 3#5) (h30 : i ≠ 30#5) :
      r (.GPR i) t = r (.GPR i) u := by
    simpa [memsetCalled, state_simp_rules, h30] using
      preserved (.GPR i) ⟨h2, h3⟩
  refine ⟨10 + (1 + Memset.fuel (r (.GPR 2#5) u).toNat), t, ?_, ?_⟩
  · rw [run_plus, runU, runT]
  · refine ⟨pc, error, program.trans effect.program,
      (reg 20#5 (by decide) (by decide) (by decide)).trans effect.pointer,
      (reg 24#5 (by decide) (by decide) (by decide)).trans effect.result,
      (reg 26#5 (by decide) (by decide) (by decide)).trans effect.left,
      (reg 27#5 (by decide) (by decide) (by decide)).trans effect.right,
      (reg 28#5 (by decide) (by decide) (by decide)).trans effect.payload,
      (reg 23#5 (by decide) (by decide) (by decide)).trans effect.rowEnd,
      (reg 25#5 (by decide) (by decide) (by decide)).trans effect.rowNext, ?_, ?_, ?_⟩
    · intro i hi
      have hs : i ∉ [0#5, 1#5, 20#5, 23#5, 24#5, 25#5, 26#5, 27#5, 28#5] := by
        simp_all
      have h2 : i ≠ 2#5 := by simp_all
      have h3 : i ≠ 3#5 := by simp_all
      have h30 : i ≠ 30#5 := by simp_all
      exact (reg i h2 h3 h30).trans (effect.registers i hs)
    · intro i hi
      have h := preserved (.SFP i) hi
      have callFrame : r (.SFP i) (memsetCalled u base) = r (.SFP i) u := by
        unfold memsetCalled
        rw [r_of_w_different (show StateField.SFP i ≠ .GPR 30#5 from by intro h; cases h),
          r_of_w_different (show StateField.SFP i ≠ .PC from by intro h; cases h)]
      exact (h.trans callFrame).trans (effect.vectors i)
    · intro a
      rw [memory a, effect.memory, effect.destination, effect.pointer, effect.zero, r2]
      rfl

theorem ReserveZeroState.zero_bytes {s t : ArmState} {base : BitVec 64}
    (post : ReserveZeroState s t base) (a : BitVec 64)
    (inside : (r (.GPR 20#5) t).toNat ≤ a.toNat ∧
      a.toNat < (r (.GPR 20#5) t).toNat + (r (.GPR 2#5) s).toNat) : t.mem a = 0#8 := by
  rw [post.memory, Memset.image, if_pos]
  simpa only [post.pointer] using inside

theorem ReserveZeroState.frame {s t : ArmState} {base : BitVec 64}
    (post : ReserveZeroState s t base)
    (physical : (r (.GPR 5#5) s + 16#64).toNat + 8 ≤ 2^64) :
    Delimited.MemoryFrame [((r (.GPR 5#5) s + 16#64).toNat, 8),
      ((r (.GPR 20#5) t).toNat, (r (.GPR 2#5) s).toNat)] s t := by
  intro a outside
  have cursor := outside ((r (.GPR 5#5) s + 16#64).toNat, 8) (by simp)
  have payload := outside ((r (.GPR 20#5) t).toNat, (r (.GPR 2#5) s).toNat) (by simp)
  rw [post.pointer] at payload
  rw [post.memory, Memset.image, if_neg (by omega)]
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ a physical cursor

end SszArm.NatMul
