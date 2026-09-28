import SszArm.NatMulReserveChecks
import SszArm.NatCompareMemory
import SszArm.DelimitedMemory

namespace SszArm.NatMul

/-- The size prefix restores its lowering scratch and SP on every exit. -/
structure ReserveSizeFrame (s t : ArmState) : Prop where
  program : t.program = s.program
  error : read_err t = read_err s
  registers : ∀ reg : BitVec 5, reg ∉ [2#5, 10#5, 19#5] →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s

theorem ReserveSizeFrame.trans {s t u : ArmState} (st : ReserveSizeFrame s t)
    (tu : ReserveSizeFrame t u) : ReserveSizeFrame s u :=
  ⟨tu.program.trans st.program, tu.error.trans st.error,
    fun reg hr => (tu.registers reg hr).trans (st.registers reg hr),
    fun reg => (tu.vectors reg).trans (st.vectors reg)⟩

theorem ReserveSizeFrame.sp {s t : ArmState} (h : ReserveSizeFrame s t) :
    r (.GPR 31#5) t = r (.GPR 31#5) s := h.registers _ (by decide)

theorem ReserveSizeFrame.aligned {s t : ArmState} (h : ReserveSizeFrame s t)
    (ha : CheckSPAlignment s) : CheckSPAlignment t := by
  simpa only [CheckSPAlignment, state_simp_rules, h.sp] using ha

theorem ReserveSizeFrame.code {s t : ArmState} (h : ReserveSizeFrame s t)
    (base : BitVec 64) (hc : CodeAt s base) : CodeAt t base := by
  intro row hr
  simpa only [h.program] using hc row hr

def reserveCount (s : ArmState) : Nat :=
  (r (.GPR 21#5) s).toNat + (r (.GPR 22#5) s).toNat

def reserveSumOps : List Op := [.p412, .p416]
def reserveLimitOps : List Op := [.p420, .p424]
def reserveBytes (s : ArmState) : BitVec 64 := r (.GPR 19#5) s <<< 3

def reserveSpill (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (r (.GPR 9#5) s) s

def reserveLayoutOps (s : ArmState) : List Op :=
  [.p428, .p432, .p436, .p440, .p444] ++
    if reserveBytes s &&& 9223372036854775808#64 = 0#64
    then [.p448, .p452, .p456] else [.p460, .p464, .p468]

private def reserveSizeReadOps : List Op :=
  [.p412, .p416, .p420, .p424, .p428, .p432, .p440, .p444,
   .p448, .p452, .p456, .p460, .p464, .p468]

private theorem reserve_size_read_mem (op : Op) (member : op ∈ reserveSizeReadOps)
    (base : BitVec 64) (s : ArmState) : (op.effect base s).mem = s.mem := by
  simp only [reserveSizeReadOps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Op.effect, put, next, state_simp_rules]

private theorem reserve_size_read_block (base : BitVec 64) (ops : List Op)
    (allowed : ∀ op ∈ ops, op ∈ reserveSizeReadOps) (s : ArmState) :
    (block base ops s).mem = s.mem :=
  reserve_block_preserves (fun t => t.mem) base ops
    (fun op member t => reserve_size_read_mem op (allowed op member) base t) s

private theorem reserve_size_vector (base : BitVec 64) (ops : List Op)
    (s : ArmState) (reg : BitVec 5) :
    r (.SFP reg) (block base ops s) = r (.SFP reg) s :=
  reserve_block_preserves (r (.SFP reg)) base ops (fun op _ t => op.sfp base t reg) s

private theorem reserve_size_initial_frame (base : BitVec 64) (ops : List Op)
    (allowed : ∀ op ∈ ops, op ∈ [.p412, .p416, .p420, .p424]) (s : ArmState) :
    ReserveSizeFrame s (block base ops s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_, reserve_size_vector base ops s⟩
  intro reg hr
  apply reserve_block_preserves (r (.GPR reg)) base ops
  intro op member t
  have hop := allowed op member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]

private theorem reserve_block_cons (base : BitVec 64) (op : Op)
    (ops : List Op) (s : ArmState) :
    block base (op :: ops) s = block base ops (op.effect base s) := rfl

private theorem reserve_layout_split (s : ArmState) (base : BitVec 64) :
    block base (reserveLayoutOps s) s =
      block base (if reserveBytes s &&& 9223372036854775808#64 = 0#64
        then [.p440, .p444, .p448, .p452, .p456]
        else [.p440, .p444, .p460, .p464, .p468])
        (Op.p436.effect base (block base [.p428, .p432] s)) := by
  unfold reserveLayoutOps
  split <;>
    simp only [block, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem reserve_layout_mem (s : ArmState) (base : BitVec 64) :
    (block base (reserveLayoutOps s) s).mem = (reserveSpill s).mem := by
  have before : (block base [.p428, .p432] s).mem = s.mem :=
    reserve_size_read_block base _ (by simp [reserveSizeReadOps]) s
  have address : r (.GPR 31#5) (block base [.p428, .p432] s) =
      r (.GPR 31#5) s - 16#64 := by
    simp [block, Op.effect, put, next, state_simp_rules]
  have value : r (.GPR 9#5) (block base [.p428, .p432] s) = r (.GPR 9#5) s := by
    simp [block, Op.effect, put, next, state_simp_rules]
  have stored (t : ArmState) :
      (Op.p436.effect base t).mem =
        (write_mem_bytes 8 (r (.GPR 31#5) t) (r (.GPR 9#5) t) t).mem := by
    simp [Op.effect, next, state_simp_rules]
  rw [reserve_layout_split]
  split
  ·
    rw [reserve_size_read_block base _ (by simp [reserveSizeReadOps]), stored, address, value]
    exact mem_write_mem_bytes_of_mem_eq before _ _ _
  ·
    rw [reserve_size_read_block base _ (by simp [reserveSizeReadOps]), stored, address, value]
    exact mem_write_mem_bytes_of_mem_eq before _ _ _

private theorem reserve_layout_other (s : ArmState) (base : BitVec 64)
    (reg : BitVec 5) (hr : reg ∉ [2#5, 9#5, 31#5]) :
    r (.GPR reg) (block base (reserveLayoutOps s) s) = r (.GPR reg) s := by
  apply reserve_block_preserves (r (.GPR reg)) base (reserveLayoutOps s)
  intro op member t
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  unfold reserveLayoutOps at member
  split at member <;>
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := simp_all) [Op.effect, put, next, state_simp_rules]

private theorem reserve_layout_sp (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (block base (reserveLayoutOps s) s) = r (.GPR 31#5) s := by
  unfold reserveLayoutOps
  split <;> simp [block, Op.effect, put, next, state_simp_rules, BitVec.sub_add_cancel]

private theorem reserve_layout_scratch (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    r (.GPR 9#5) (block base (reserveLayoutOps s) s) = r (.GPR 9#5) s := by
  have restore : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (reserveSpill s) =
      r (.GPR 9#5) s :=
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)
  simp only [reserveSpill] at restore
  unfold reserveLayoutOps
  split <;> simp_all [reserveBytes, block, Op.effect, put, next, state_simp_rules,
    NatCompare.read_spill_w, BitVec.sub_add_cancel]

private theorem reserve_layout_frame (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ReserveSizeFrame s (block base (reserveLayoutOps s) s) := by
  refine ⟨block_program _ _ _, block_error _ _ _, ?_,
    reserve_size_vector base (reserveLayoutOps s) s⟩
  intro reg hr
  by_cases sp : reg = 31#5
  · subst reg
    exact reserve_layout_sp s base
  · by_cases scratch : reg = 9#5
    · subst reg
      exact reserve_layout_scratch s base hs
    · exact reserve_layout_other s base reg (by simp_all)

theorem reserve_sum_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 412#64) :
    run 2 s = block base reserveSumOps s := by
  apply block_run base reserveSumOps s hc he ha
  have hpc : r .PC s = base + 412#64 := hp
  simp [reserveSumOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem reserve_sum_effect (s : ArmState) (base : BitVec 64) :
    let t := block base reserveSumOps s
    read_pc t = (if 2^64 ≤ reserveCount s then base + 1344#64 else base + 420#64) ∧
      r (.GPR 19#5) t = r (.GPR 22#5) s + r (.GPR 21#5) s ∧
      t.mem = s.mem ∧ ReserveSizeFrame s t := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [reserveSumOps, reserveCount, block, Op.effect, put, next,
      state_simp_rules, Udivti3.adc_carry, Udivti3.radix, Nat.add_comm]
  · simp [reserveSumOps, block, Op.effect, put, next, state_simp_rules]
  · exact reserve_size_read_block base reserveSumOps
      (by simp [reserveSumOps, reserveSizeReadOps]) s
  · exact reserve_size_initial_frame base reserveSumOps (by simp [reserveSumOps]) s

theorem reserve_limit_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 420#64) :
    run 2 s = block base reserveLimitOps s := by
  apply block_run base reserveLimitOps s hc he ha
  have hpc : r .PC s = base + 420#64 := hp
  simp [reserveLimitOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem reserve_limit_effect (s : ArmState) (base : BitVec 64) :
    let t := block base reserveLimitOps s
    read_pc t = (if (r (.GPR 19#5) s).toNat < 2^61
      then base + 428#64 else base + 1076#64) ∧
      r (.GPR 19#5) t = r (.GPR 19#5) s ∧ t.mem = s.mem ∧ ReserveSizeFrame s t := by
  have shift : r (.GPR 19#5) s >>> 61 = 0#64 ↔ (r (.GPR 19#5) s).toNat < 2^61 := by
    bv_omega
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [reserveLimitOps, block, Op.effect, put, next, state_simp_rules, shift]
  · simp [reserveLimitOps, block, Op.effect, put, next, state_simp_rules]
  · exact reserve_size_read_block base reserveLimitOps
      (by simp [reserveLimitOps, reserveSizeReadOps]) s
  · exact reserve_size_initial_frame base reserveLimitOps (by simp [reserveLimitOps]) s

theorem reserve_layout_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 428#64) :
    run 8 s = block base (reserveLayoutOps s) s := by
  have length : (reserveLayoutOps s).length = 8 := by
    unfold reserveLayoutOps
    split <;> rfl
  rw [← length]
  apply block_run base (reserveLayoutOps s) s hc he ha
  have hpc : r .PC s = base + 428#64 := hp
  unfold reserveLayoutOps
  split <;> simp_all [reserveBytes, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, BitVec.add_assoc]

private theorem reserve_layout_two (s : ArmState) (base : BitVec 64) :
    r (.GPR 2#5) (block base (reserveLayoutOps s) s) = reserveBytes s := by
  have tailPres (ops : List Op)
      (allowed : ∀ op ∈ ops, op ∈
        [.p432, .p436, .p440, .p444, .p448, .p452, .p456, .p460, .p464, .p468])
      (t : ArmState) : r (.GPR 2#5) (block base ops t) = r (.GPR 2#5) t := by
    apply reserve_block_preserves (r (.GPR 2#5)) base ops
    intro op member u
    have hop := allowed op member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Op.effect, put, next, state_simp_rules]
  unfold reserveLayoutOps
  split <;> simp only [List.cons_append, List.nil_append]
  all_goals
    rw [reserve_block_cons, tailPres _ (by simp)]
    simp [reserveBytes, Op.effect, put, next, state_simp_rules]

private theorem reserve_layout_pc (s : ArmState) (base : BitVec 64) :
    read_pc (block base (reserveLayoutOps s) s) =
      if (reserveBytes s).toNat < 2^63 then base + 472#64 else base + 1076#64 := by
  have high := SszNative.Arena.high_bit_clear (reserveBytes s)
  unfold reserveLayoutOps
  split <;> simp_all [reserveBytes, block, Op.effect, put, next,
    state_simp_rules, BitVec.sub_add_cancel, BitVec.add_assoc]

theorem reserve_layout_effect (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    let t := block base (reserveLayoutOps s) s
    read_pc t = (if (reserveBytes s).toNat < 2^63 then base + 472#64 else base + 1076#64) ∧
      r (.GPR 19#5) t = r (.GPR 19#5) s ∧ r (.GPR 2#5) t = reserveBytes s ∧
      t.mem = (reserveSpill s).mem ∧ ReserveSizeFrame s t :=
  ⟨reserve_layout_pc s base, reserve_layout_other s base 19#5 (by decide),
    reserve_layout_two s base, reserve_layout_mem s base, reserve_layout_frame s base hs⟩

theorem reserve_layout_memory (s : ArmState) (base : BitVec 64)
    (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)]
      s (block base (reserveLayoutOps s) s) := by
  intro a outside
  rw [(reserve_layout_effect s base hs).2.2.2.1]
  have h := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp)
  exact BoolCodec.write_mem_bytes_frame s _ 8 _ a (by bv_omega) (by bv_omega)

theorem reserve_bytes (s : ArmState) (bound : (r (.GPR 19#5) s).toNat < 2^61) :
    (reserveBytes s).toNat = 8 * (r (.GPR 19#5) s).toNat := by
  simp only [reserveBytes, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- Complete original usize, shift-width and signed-layout guards, including the
actual X9 lowering spill. No logical operand-count cap is assumed. -/
theorem reserve_size_runs (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 412#64) (hs : 16 ≤ (r (.GPR 31#5) s).toNat) :
    ∃ fuel t, run fuel s = t ∧ ReserveSizeFrame s t ∧
      Delimited.MemoryFrame [((r (.GPR 31#5) s).toNat - 16, 16)] s t ∧
      ((2^64 ≤ reserveCount s ∧ read_pc t = base + 1344#64) ∨
       (¬ 8 * reserveCount s < 2^63 ∧ read_pc t = base + 1076#64) ∨
       (8 * reserveCount s < 2^63 ∧ read_pc t = base + 472#64 ∧
        (r (.GPR 19#5) t).toNat = reserveCount s ∧
        (r (.GPR 2#5) t).toNat = 8 * reserveCount s)) := by
  let a := block base reserveSumOps s
  have ar := reserve_sum_run s base hc he ha hp
  have ae := reserve_sum_effect s base
  by_cases sum : reserveCount s < 2^64
  · have ap : read_pc a = base + 420#64 := ae.1.trans (if_neg (by omega))
    have count : (r (.GPR 19#5) a).toNat = reserveCount s := by
      rw [ae.2.1, BitVec.toNat_add]
      dsimp [reserveCount] at *
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    let b := block base reserveLimitOps a
    have br := reserve_limit_run a base (ae.2.2.2.code base hc)
      (ae.2.2.2.error.trans he) (ae.2.2.2.aligned ha) ap
    have be := reserve_limit_effect a base
    have frame := ae.2.2.2.trans be.2.2.2
    have memory : b.mem = s.mem := be.2.2.1.trans ae.2.2.1
    by_cases width : reserveCount s < 2^61
    · have bp : read_pc b = base + 428#64 := be.1.trans (if_pos (by rw [count]; exact width))
      have bcount : (r (.GPR 19#5) b).toNat = reserveCount s :=
        (congrArg BitVec.toNat be.2.1).trans count
      have bsp := frame.sp
      have bs : 16 ≤ (r (.GPR 31#5) b).toNat := by rw [bsp]; exact hs
      let t := block base (reserveLayoutOps b) b
      have tr := reserve_layout_run b base (frame.code base hc)
        (frame.error.trans he) (frame.aligned ha) bp
      have te := reserve_layout_effect b base bs
      have bytes : (reserveBytes b).toNat = 8 * reserveCount s := by
        rw [reserve_bytes b (by rw [bcount]; exact width), bcount]
      refine ⟨(2 + 2) + 8, t, ?_, frame.trans te.2.2.2.2, ?_, ?_⟩
      · rw [run_plus, run_plus, ar, br, tr]
      · intro address outside
        rw [← memory]
        exact reserve_layout_memory b base bs address (by rw [bsp]; exact outside)
      · by_cases layout : 8 * reserveCount s < 2^63
        · exact Or.inr (Or.inr ⟨layout, te.1.trans (if_pos (by rw [bytes]; exact layout)),
            (congrArg BitVec.toNat te.2.1).trans bcount,
            (congrArg BitVec.toNat te.2.2.1).trans bytes⟩)
        · exact Or.inr (Or.inl ⟨layout, te.1.trans (if_neg (by rw [bytes]; exact layout))⟩)
    · refine ⟨2 + 2, b, ?_, frame, ?_, Or.inr (Or.inl ⟨by omega, ?_⟩)⟩
      · rw [run_plus, ar, br]
      · intro address outside
        rw [memory]
      · exact be.1.trans (if_neg (by rw [count]; exact width))
  · refine ⟨2, a, ar, ae.2.2.2, ?_, Or.inl ⟨by omega, ae.1.trans (if_pos (by omega))⟩⟩
    intro address outside
    rw [ae.2.2.1]

end SszArm.NatMul
