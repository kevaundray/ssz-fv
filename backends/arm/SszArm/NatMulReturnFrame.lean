import SszArm.NatMulRestore
import SszArm.NatMulContract
import SszArm.NatMulWordReturnValues
import SszArm.NatMulWordReturnError

namespace SszArm.NatMul

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

/-- Current main frame: the lowering slot is below the 96 saved bytes. -/
structure ReturnSpace (s : ArmState) (out : BitVec 64) : Prop where
  stack : 16 ≤ (r (.GPR 31#5) s).toNat
  savedBound : (r (.GPR 31#5) s).toNat + 96 ≤ 2^64
  output : out.toNat + 72 ≤ 2^64
  separate : out.toNat + 72 ≤ (r (.GPR 31#5) s).toNat - 16 ∨
    (r (.GPR 31#5) s).toNat + 96 ≤ out.toNat

def returnWrites (s : ArmState) (out : BitVec 64) : List Span :=
  [(out.toNat, 16), (out.toNat + 64, 4), ((r (.GPR 31#5) s).toNat - 16, 16)]

def returnErrorWrites (s : ArmState) (out : BitVec 64) : List Span :=
  [(out.toNat, 68), ((r (.GPR 31#5) s).toNat - 16, 16)]

theorem ReturnSpace.word {s : ArmState} (space : ReturnSpace s (r (.GPR 0#5) s)) :
    NatMulWord.ReturnOwned s :=
  ⟨space.stack, space.output, space.separate.imp id (by omega)⟩

theorem ReturnSpace.saved_protected {s : ArmState} {out : BitVec 64}
    (space : ReturnSpace s out) :
    Protected (returnErrorWrites s out) (r (.GPR 31#5) s).toNat 96 := by
  right
  intro span member
  simp only [returnErrorWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  have := space.stack
  have := space.separate
  rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem return_frame_widen {s t : ArmState} {out : BitVec 64}
    (frame : MemoryFrame (returnWrites s out) s t) :
    MemoryFrame (returnErrorWrites s out) s t := by
  intro a outside
  apply frame a
  intro span member
  have ho := outside (out.toNat, 68) (by simp [returnErrorWrites])
  have hs := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [returnErrorWrites])
  simp only [returnWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at * <;> omega

theorem Saved.return_frame {entry s t : ArmState} {out : BitVec 64}
    (saved : Saved entry s) (space : ReturnSpace s out)
    (frame : MemoryFrame (returnErrorWrites s out) s t)
    (sp : r (.GPR 31#5) t = r (.GPR 31#5) s)
    (x29 : r (.GPR 29#5) t = r (.GPR 29#5) s)
    (vectors : ∀ reg, r (.SFP reg) t = r (.SFP reg) s) : Saved entry t := by
  refine ⟨sp.trans saved.sp, ?_, x29.trans saved.x29, ?_⟩
  · intro reg offset member
    have bound : offset + 8 ≤ 96 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with h | h | h | h | h | h | h | h | h | h | h
      all_goals cases h <;> decide
    rw [sp]
    have physical := space.savedBound
    have same := frame.load ((r (.GPR 31#5) s).toNat + offset) 8 (by omega)
      (space.saved_protected.subspan offset 8 bound)
    have bytes : read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) t =
        read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 offset) s := by
      apply BitVec.eq_of_toNat_eq
      simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat] using Option.some.inj same
    exact bytes.trans (saved.words reg offset member)
  · intro reg low high
    rw [vectors]
    exact saved.vectors reg low high

theorem ReturnSpace.of_owned {entry s : ArmState} {left right : SszNative.NatOperand}
    (owned : Owned entry left right) (saved : Saved entry s) :
    ReturnSpace s (r (.GPR 0#5) entry) := by
  have stack := owned.stackBound
  have sp : (r (.GPR 31#5) s).toNat = (r (.GPR 31#5) entry).toNat - 96 := by
    rw [saved.sp]
    bv_omega
  refine ⟨by rw [sp]; omega, ?_, owned.outputBound, ?_⟩
  · rw [sp]
    have := (r (.GPR 31#5) entry).isLt
    omega
  · rcases owned.outputStack with empty | separate
    · omega
    · have apart := separate ((r (.GPR 31#5) entry).toNat - 144, 144) (by simp)
      simp only [Prod.fst, Prod.snd] at apart
      rw [sp]
      omega

end SszArm.NatMul
