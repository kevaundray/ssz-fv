import SszArm.NatMulWordReserveLarge
import SszArm.NatAddMemory

namespace SszArm.NatMulWord.Reserve

def firstLoadOps : List Op := [.p452, .p456, .p460]
def firstFinishOps : List Op := [.p464, .p468, .p472, .p476]
def firstOps : List Op := firstLoadOps ++ firstFinishOps

def firstMemory (s : ArmState) : ArmState :=
  write_mem_bytes 8 (r (.GPR 4#5) s + 16#64) (r (.GPR 17#5) s) s

theorem first_block (s : ArmState) (base : BitVec 64) :
    block base firstOps s = block base firstFinishOps (block base firstLoadOps s) := by
  simp only [block, firstOps, List.foldl_append]

theorem first_load_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (keep : reg ∉ [1#5, 10#5, 13#5, 14#5]) :
    r (.GPR reg) (block base firstLoadOps s) = r (.GPR reg) s := by
  apply block_preserves (r (.GPR reg)) base firstLoadOps
  intro op member t
  simp only [firstLoadOps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp_all [Op.effect, put, next, state_simp_rules]

theorem first_finish_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (keep : reg ∉ [11#5, 12#5, 15#5]) :
    r (.GPR reg) (block base firstFinishOps s) = r (.GPR reg) s := by
  apply block_preserves (r (.GPR reg)) base firstFinishOps
  intro op member t
  simp only [firstFinishOps, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp_all [Op.effect, put, next, state_simp_rules]

theorem first_registers (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (keep : reg ∉ [1#5, 10#5, 11#5, 12#5, 13#5, 14#5, 15#5]) :
    r (.GPR reg) (block base firstOps s) = r (.GPR reg) s := by
  rw [first_block,
    first_finish_registers _ base reg (by simp_all),
    first_load_registers s base reg (by simp_all)]

theorem first_load_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 452#64) :
    let t := block base firstLoadOps s
    read_pc t = base + 464#64 ∧
      r (.GPR 1#5) t = r (.GPR 1#5) s + 8#64 ∧
      r (.GPR 14#5) t = read_mem_bytes 8 (r (.GPR 1#5) s) s ∧
      r (.GPR 13#5) t = 0#64 ∧
      r (.GPR 10#5) t = r (.GPR 10#5) s + r (.GPR 16#5) s ∧ t.mem = s.mem := by
  have hpc : r .PC s = base + 452#64 := hp
  simp [firstLoadOps, block, Op.effect, put, next, state_simp_rules, hpc, BitVec.add_assoc]

theorem first_finish_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 464#64) :
    let t := block base firstFinishOps s
    read_pc t = base + 480#64 ∧
      r (.GPR 12#5) t = r (.GPR 12#5) s + 3#64 ∧
      r (.GPR 15#5) t = r (.GPR 15#5) s + 8#64 ∧
      r (.GPR 11#5) t = r (.GPR 14#5) s * r (.GPR 3#5) s ∧
      t.mem = (firstMemory s).mem := by
  have hpc : r .PC s = base + 464#64 := hp
  simp [firstFinishOps, firstMemory, block, Op.effect, put, next, state_simp_rules,
    hpc, BitVec.add_assoc, NatCompare.spill_mem_w]

theorem first_run (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base + 452#64) :
    run 7 s = block base firstOps s := by
  have loadRun : run 3 s = block base firstLoadOps s := by
    apply block_run base firstLoadOps s hc he ha
    have hpc : r .PC s = base + 452#64 := hp
    simp [firstLoadOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  let u := block base firstLoadOps s
  have upc : read_pc u = base + 464#64 := (first_load_effect s base hp).1
  have finishRun : run 4 u = block base firstFinishOps u := by
    apply block_run base firstFinishOps u
      (by simpa only [u, CodeAt, block_program] using hc)
      (by simpa only [u, block_error] using he) (block_aligned base firstLoadOps s ha)
    have hpc : r .PC u = base + 464#64 := upc
    simp [firstFinishOps, Follows, Op.row, Op.effect, put, next, state_simp_rules,
      hpc, BitVec.add_assoc]
  change run (3 + 4) s = _
  rw [run_plus, loadRun, finishRun, first_block]

/-- The initial source load precedes the cursor store. No output-limb store has
occurred yet; PC480 is exactly the first high-product lowering activation. -/
theorem first_effect (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 452#64) :
    let t := block base firstOps s
    read_pc t = base + 480#64 ∧
      r (.GPR 1#5) t = r (.GPR 1#5) s + 8#64 ∧
      r (.GPR 14#5) t = read_mem_bytes 8 (r (.GPR 1#5) s) s ∧
      r (.GPR 13#5) t = 0#64 ∧
      r (.GPR 10#5) t = r (.GPR 10#5) s + r (.GPR 16#5) s ∧
      r (.GPR 12#5) t = r (.GPR 12#5) s + 3#64 ∧
      r (.GPR 15#5) t = r (.GPR 15#5) s + 8#64 ∧
      r (.GPR 11#5) t = read_mem_bytes 8 (r (.GPR 1#5) s) s * r (.GPR 3#5) s ∧
      t.mem = (firstMemory s).mem := by
  let u := block base firstLoadOps s
  have load := first_load_effect s base hp
  have finish := first_finish_effect u base load.1
  rw [first_block]
  refine ⟨finish.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (first_finish_registers u base 1#5 (by decide)).trans load.2.1
  · exact (first_finish_registers u base 14#5 (by decide)).trans load.2.2.1
  · exact (first_finish_registers u base 13#5 (by decide)).trans load.2.2.2.1
  · exact (first_finish_registers u base 10#5 (by decide)).trans load.2.2.2.2.1
  · rw [finish.2.1, first_load_registers s base 12#5 (by decide)]
  · rw [finish.2.2.1, first_load_registers s base 15#5 (by decide)]
  · rw [finish.2.2.2.1, load.2.2.1, first_load_registers s base 3#5 (by decide)]
  · apply finish.2.2.2.2.trans
    unfold firstMemory
    rw [first_load_registers s base 4#5 (by decide), first_load_registers s base 17#5 (by decide)]
    exact mem_write_mem_bytes_of_mem_eq load.2.2.2.2.2 _ _ _

theorem first_memory (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 452#64)
    (physical : (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64) :
    let t := block base firstOps s
    Delimited.MemoryFrame [((r (.GPR 4#5) s + 16#64).toNat, 8)] s t ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 16#64) t = r (.GPR 17#5) s := by
  have hm := (first_effect s base hp).2.2.2.2.2.2.2.2
  constructor
  · intro a outside
    rw [hm]
    exact BoolCodec.write_mem_bytes_frame _ _ _ _ a physical
      (outside ((r (.GPR 4#5) s + 16#64).toNat, 8) (by simp))
  · rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ physical

theorem first_header (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 452#64)
    (physical : (r (.GPR 4#5) s).toNat + 24 ≤ 2^64) :
    let t := block base firstOps s
    read_mem_bytes 8 (r (.GPR 4#5) s) t = read_mem_bytes 8 (r (.GPR 4#5) s) s ∧
      read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) t =
        read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) s := by
  have hm := (first_effect s base hp).2.2.2.2.2.2.2.2
  constructor
  all_goals
    rw [Memory.mem_eq_iff_read_mem_bytes_eq.mp hm]
    apply BoolCodec.read_mem_bytes_write_mem_bytes_disjoint
    all_goals bv_omega

theorem first_input (s : ArmState) (base : BitVec 64)
    (hp : read_pc s = base + 452#64)
    (physical : (r (.GPR 4#5) s + 16#64).toNat + 8 ≤ 2^64)
    (operand : SszNative.NatOperand) (input : operand.At (UintCodec.widthLoad s))
    (owned : NatAdd.OperandOwned [((r (.GPR 4#5) s + 16#64).toNat, 8)] operand) :
    NatAdd.OperandPreserved s (block base firstOps s) operand :=
  NatAdd.operand_preserved (first_memory s base hp physical).1 operand input owned

theorem first_checked_pointer (s : ArmState) (base address capacity used : BitVec 64)
    (hp : read_pc s = base + 452#64) (words : Nat)
    (checks : SszNative.Arena.Checks address.toNat capacity.toNat used.toNat words)
    (addressReg : r (.GPR 10#5) s = address)
    (startReg : (r (.GPR 16#5) s).toNat = SszNative.Arena.start address.toNat used.toNat) :
    (r (.GPR 10#5) (block base firstOps s)).toNat =
      address.toNat + SszNative.Arena.start address.toNat used.toNat := by
  rw [(first_effect s base hp).2.2.2.2.1]
  exact header_pointer .large words s address capacity used checks addressReg startReg

end SszArm.NatMulWord.Reserve
