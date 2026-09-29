import SszArm.NatMulReturnFrame

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (MemoryFrame Returned)

def zeroReturnOps : List Op :=
  [.p264, .p268, .p272, .p276, .p280, .p284, .p288, .p292, .p296, .p300,
   .p304, .p308, .p312, .p316, .p320, .p324, .p328, .p332, .p336, .p340, .p344]

def zeroReturnBody (s : ArmState) (base : BitVec 64) : ArmState :=
  block base zeroReturnOps s

private def wordZeroOps : List NatMulWord.Op :=
  NatMulWord.valueOps .zero ++ (NatMulWord.StatusPath.ops .zero).take 10

private theorem zero_word_prefix (s : ArmState) (base : BitVec 64) :
    zeroReturnBody s base = NatMulWord.block base wordZeroOps s := by
  have effects : zeroReturnOps.map (Op.effect base) =
      wordZeroOps.map (NatMulWord.Op.effect base) := by
    simp only [zeroReturnOps, wordZeroOps, NatMulWord.valueOps, NatMulWord.StatusPath.ops,
      List.take, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.cons.injEq, and_true]
    repeat' apply And.intro
    all_goals
      funext t
      rfl
  simpa only [zeroReturnBody, block, NatMulWord.block, List.foldl_map] using
    congrArg (fun fs : List (ArmState → ArmState) => fs.foldl (fun t f => f t) s) effects

/-- The leaf sequence differs only by RET; the main image continues into its
original restore sequence. -/
theorem zero_return_erased (s : ArmState) (base : BitVec 64) :
    w .PC 0#64 (zeroReturnBody s base) =
      w .PC 0#64 (NatMulWord.valueResult .zero base s) := by
  have append (xs ys : List NatMulWord.Op) (t : ArmState) :
      NatMulWord.block base (xs ++ ys) t =
        NatMulWord.block base ys (NatMulWord.block base xs t) := by
    simp only [NatMulWord.block, List.foldl_append]
  have split : NatMulWord.valueOps .zero ++ NatMulWord.StatusPath.ops .zero =
      wordZeroOps ++ [.p96] := rfl
  have leaf : NatMulWord.valueResult .zero base s =
      NatMulWord.block base [.p96] (NatMulWord.block base wordZeroOps s) := by
    unfold NatMulWord.valueResult NatMulWord.statusResult NatMulWord.valueBody
    rw [← append, split, append]
  have tail (t : ArmState) :
      w .PC 0#64 t = w .PC 0#64 (NatMulWord.block base [.p96] t) := by
    simp only [NatMulWord.block, List.foldl_cons, List.foldl_nil,
      NatMulWord.Op.effect, state_simp_rules]
  rw [zero_word_prefix, leaf]
  exact tail _

theorem zero_return_body_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 264#64) : run 21 s = zeroReturnBody s base := by
  apply block_run base zeroReturnOps s code error aligned
  have hpc : r .PC s = base + 264#64 := pc
  simp [zeroReturnOps, Follows, Op.row, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem zero_return_body_pc (s : ArmState) (base : BitVec 64)
    (pc : read_pc s = base + 264#64) : read_pc (zeroReturnBody s base) = base + 348#64 := by
  have hpc : r .PC s = base + 264#64 := pc
  simp [zeroReturnBody, zeroReturnOps, block, Op.effect, put, next,
    state_simp_rules, hpc, BitVec.add_assoc]

theorem zero_return_body_frame (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    MemoryFrame (returnWrites s (r (.GPR 0#5) s)) s (zeroReturnBody s base) := by
  have memory := congrArg ArmState.mem (zero_return_erased s base)
  simp only [ArmState.mem_w_eq_mem] at memory
  intro a outside
  rw [memory]
  exact NatMulWord.value_frame .zero s base space.word a outside

theorem zero_return_body_registers (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) (reg : BitVec 5) :
    r (.GPR reg) (zeroReturnBody s base) = r (.GPR reg) s := by
  have same := congrArg (r (.GPR reg)) (zero_return_erased s base)
  rw [r_of_w_different (show StateField.GPR reg ≠ .PC by intro h; cases h),
    r_of_w_different (show StateField.GPR reg ≠ .PC by intro h; cases h)] at same
  exact same.trans (NatMulWord.value_registers .zero s base space.word reg)

theorem zero_return_body_image (s : ArmState) (base : BitVec 64)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    SszNative.NatArithmetic.AddResultAt (widthLoad (zeroReturnBody s base))
      (r (.GPR 0#5) s).toNat (.ok (.small 0#64)) := by
  have memory := congrArg ArmState.mem (zero_return_erased s base)
  simp only [ArmState.mem_w_eq_mem] at memory
  have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp memory
  have observed : widthLoad (zeroReturnBody s base) =
      widthLoad (NatMulWord.valueResult .zero base s) := by
    funext a n
    simp only [widthLoad, loads]
  rw [observed]
  exact NatMulWord.value_small_image .zero s base 0#64 space.word rfl rfl

def zeroReturned (s : ArmState) (base : BitVec 64) : ArmState :=
  restored .return (zeroReturnBody s base) base

theorem zero_return_run (entry s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 264#64) (saved : Saved entry s)
    (space : ReturnSpace s (r (.GPR 0#5) s)) :
    run 28 s = zeroReturned s base ∧ Returned entry (zeroReturned s base) ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad (zeroReturned s base))
        (r (.GPR 0#5) s).toNat (.ok (.small 0#64)) ∧
      MemoryFrame (returnWrites s (r (.GPR 0#5) s)) s (zeroReturned s base) := by
  have bodyFrame := zero_return_body_frame s base space
  have bodySaved := saved.return_frame space (return_frame_widen bodyFrame)
    (zero_return_body_registers s base space 31#5)
    (zero_return_body_registers s base space 29#5)
    (by intro reg; simp [zeroReturnBody, zeroReturnOps, block, Op.effect, put, next, state_simp_rules])
  have bodyError : read_err (zeroReturnBody s base) = .None :=
    (block_error base zeroReturnOps s).trans error
  refine ⟨?_, return_restored entry _ base bodySaved bodyError, ?_, ?_⟩
  · rw [show 28 = 21 + 7 by decide, run_plus, zero_return_body_run s base code error aligned pc]
    exact restore_run .return _ base
      (by simpa only [zeroReturnBody, CodeAt, block_program] using code) bodyError
      (block_aligned base zeroReturnOps s aligned) (zero_return_body_pc s base pc)
  · have loads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (restore_memory .return (zeroReturnBody s base) base)
    have observed : widthLoad (zeroReturned s base) = widthLoad (zeroReturnBody s base) := by
      funext a n; simp only [zeroReturned, widthLoad, loads]
    rw [observed]
    exact zero_return_body_image s base space
  · intro a outside
    exact (congrFun (restore_memory .return (zeroReturnBody s base) base) a).trans (bodyFrame a outside)

end SszArm.NatMul
