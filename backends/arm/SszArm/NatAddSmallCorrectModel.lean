import SszArm.NatAddOneWordLoad
import SszArm.NatAddZeroOwned
import SszArm.NatAddArenaSmall
import SszArm.NatAddReturnError

namespace SszArm.NatAdd.SmallCorrect

open UintCodec SszNative
open Delimited (Protected MemoryFrame Returned)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

def low (left right : NatOperand) : BitVec 64 :=
  SszNative.NatAdd.lowWord left + SszNative.NatAdd.lowWord right

theorem wide_low (left right : NatOperand) :
    (SszNative.NatAdd.sumWide left right).setWidth 64 = low left right := by
  apply BitVec.eq_of_toNat_eq
  simp [SszNative.NatAdd.sumWide, LimbAdd.wideSum_toNat _ _ 0 (by omega),
    BitVec.toNat_setWidth, low, BitVec.toNat_add]

theorem wide_high (left right : NatOperand)
    (overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat) :
    ((SszNative.NatAdd.sumWide left right) >>> 64).setWidth 64 = 1#64 := by
  have hl := (SszNative.NatAdd.lowWord left).isLt
  have hr := (SszNative.NatAdd.lowWord right).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [SszNative.NatAdd.sumWide, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    LimbAdd.wideSum_toNat _ _ 0 (by omega), Nat.add_zero, BitVec.toNat_ofNat]
  omega

theorem model_small (s : ArmState) (left right : NatOperand)
    (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (fits : ¬ 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat) :
    outcome s left right = NatArithmetic.unchanged (arenaOf s).used (.ok (.small (low left right))) := by
  have leftValue := SszNative.NatAdd.lowWord_value left (by omega)
  have rightValue := SszNative.NatAdd.lowWord_value right (by omega)
  unfold outcome
  rw [SszNative.NatAdd.run_small left right _ _ _ (by omega) (by omega)
    ⟨by omega, by omega⟩ (by omega), wide_low]

theorem model_overflow (s : ArmState) (left right : NatOperand)
    (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat) :
    outcome s left right =
      match Arena.reserve (arenaOf s).base (arenaOf s).capacity (arenaOf s).used 2 with
      | none => NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted)
      | some reservation => NatArithmetic.committed reservation [low left right, 1#64] := by
  have leftValue := SszNative.NatAdd.lowWord_value left (by omega)
  have rightValue := SszNative.NatAdd.lowWord_value right (by omega)
  unfold outcome
  rw [SszNative.NatAdd.run_small_overflow left right _ _ _ (by omega) (by omega)
    ⟨by omega, by omega⟩ (by omega), wide_low, wide_high left right overflow]

theorem committed_pair (reservation : Arena.Reservation) (word : BitVec 64) :
    NatOperand.fromWords (BitVec.ofNat 64 reservation.pointer) [word, 1#64] =
      .large (BitVec.ofNat 64 reservation.pointer) [word, 1#64] := by
  simp [NatOperand.fromWords, Limbs.trim]

theorem prefix_trans {s u t : ArmState} (first : ZeroFrame s u) (second : ZeroFrame u t) :
    ZeroFrame s t := by
  refine ⟨second.program.trans first.program, second.error.trans first.error,
    second.out.trans first.out, second.sp.trans first.sp,
    fun reg lo hi => (second.registers reg lo hi).trans (first.registers reg lo hi),
    fun reg lo hi => (second.vectors reg lo hi).trans (first.vectors reg lo hi), ?_⟩
  exact first.memory.trans (by simpa only [first.writes] using second.memory)

theorem arena_returned {s u t : ArmState} (frame : ArenaFrame s u)
    (returned : Returned u t) : Returned s t := by
  refine ⟨returned.pc.trans (frame.registers 30#5 (by decide)), returned.error,
    returned.sp.trans frame.sp, ?_, ?_⟩
  · intro reg lo hi
    apply (returned.registers reg lo hi).trans
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat constructor <;> bv_omega
  · intro reg lo hi
    rw [returned.vectors reg lo hi, frame.vectors]

theorem arena_prefix {s t : ArmState} (frame : ArenaFrame s t) (memory : t.mem = s.mem) :
    ZeroFrame s t := by
  refine ⟨frame.program, frame.error, frame.registers _ (by decide), frame.sp, ?_, ?_, ?_⟩
  · intro reg lo hi
    apply frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    repeat constructor <;> bv_omega
  · intro reg lo hi
    rw [frame.vectors]
  · intro a ha
    exact congrFun memory a

theorem prefix_header {s t : ArmState} {left right : NatOperand}
    (owned : Owned s left right) (frame : ZeroFrame s t)
    (h5 : r (.GPR 5#5) t = r (.GPR 5#5) s) (offset : Nat) (bound : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 5#5) t + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 5#5) s + BitVec.ofNat 64 offset) s := by
  rw [h5]
  have physical := owned.arenaBound
  have address : (r (.GPR 5#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 5#5) s).toNat + offset := by bv_omega
  exact frame.memory.read _ 8 (by rw [address]; omega)
    (by rw [address]; exact owned.arenaLocal.subspan offset 8 bound)

end SszArm.NatAdd.SmallCorrect
