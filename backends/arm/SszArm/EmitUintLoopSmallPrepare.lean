import SszArm.EmitUintLoopStoreMemory
import SszArm.EmitUintLoopMath
import SszArm.Udivti3Arithmetic
import SszArm.NatExactState

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def smallPrepareOps : List ByteOp := [.p936, .p940, .p944, .p948, .p952, .p956, .p960]

@[irreducible] def smallPrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  let shift := r (.GPR 9#5) s &&& 56#64
  let word := if 8 ≤ (r (.GPR 10#5) s).toNat then 0#64 else r (.GPR 8#5) s
  w .PC (base + 964#64)
    (w (.GPR 9#5) (r (.GPR 9#5) s + 8#64)
      (w (.GPR 12#5) (word >>> (shift.toNat % 64))
        (w (.GPR 11#5) (r (.GPR 10#5) s + 1#64)
          (w (.GPR 13#5) shift
            (write_pstate (AddWithCarry (r (.GPR 1#5) s) (~~~(r (.GPR 10#5) s + 1#64)) 1#1).2 s)))))

theorem small_prepare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 936#64) : run 7 s = smallPrepared s base := by
  have position : r .PC s = base + 936#64 := pc
  have follows : ByteFollows base smallPrepareOps s := by
    simp [smallPrepareOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next,
      Dispatch.compare64, Dispatch.next, state_simp_rules, position, BitVec.add_assoc]
  rw [show 7 = smallPrepareOps.length by rfl, byte_run base smallPrepareOps s code error aligned follows]
  have carry : (AddWithCarry (r (.GPR 10#5) s) (~~~8#64) 1#1).2.c = 1#1 ↔
      8 ≤ (r (.GPR 10#5) s).toNat := Udivti3.cmp_carry _ _
  change (AddWithCarry (r (.GPR 10#5) s) 18446744073709551607#64 1#1).2.c = 1#1 ↔
    8 ≤ (r (.GPR 10#5) s).toNat at carry
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases h9 : reg = 9#5
      · subst reg
        simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
          position, BitVec.add_assoc, carry]
      · by_cases h11 : reg = 11#5
        · subst reg
          simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
            put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
            position, BitVec.add_assoc, carry]
        · by_cases h12 : reg = 12#5
          · subst reg
            simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
              put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
              position, BitVec.add_assoc, carry]
          · by_cases h13 : reg = 13#5
            · subst reg
              simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
                put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
                position, BitVec.add_assoc, carry]
            · simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
                put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
                NatExact.r_gpr_w, h9, h11, h12, h13, position, BitVec.add_assoc, carry]
    | FLAG flag =>
      cases flag <;>
        simp (config := {decide := true}) [byteBlock, smallPrepareOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, smallPrepared, state_simp_rules,
          position, BitVec.add_assoc, carry]
    | PC =>
      simp [byteBlock, smallPrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, smallPrepared, state_simp_rules, position, BitVec.add_assoc]
    | SFP reg =>
      simp [byteBlock, smallPrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, smallPrepared, state_simp_rules]
    | ERR =>
      simp [byteBlock, smallPrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, smallPrepared, state_simp_rules]
  · simp [byteBlock, smallPrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
      Dispatch.next, smallPrepared, state_simp_rules]
  · intro bytes address
    simp [byteBlock, smallPrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
      Dispatch.next, smallPrepared, state_simp_rules]

@[simp] theorem smallPrepared_memory (s : ArmState) (base : BitVec 64) :
    (smallPrepared s base).mem = s.mem := by simp [smallPrepared, state_simp_rules]

@[simp] theorem smallPrepared_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (untouched : reg ∉ [9#5, 11#5, 12#5, 13#5]) :
    r (.GPR reg) (smallPrepared s base) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp [smallPrepared, state_simp_rules, untouched.1, untouched.2.1,
    untouched.2.2.1, untouched.2.2.2]

theorem smallPrepared_frame (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) :
    Frame s (smallPrepared s base) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [smallPrepared, state_simp_rules]
  · simp [smallPrepared, state_simp_rules]
  · intro reg outside
    apply smallPrepared_register
    simp_all
  · intro reg
    simp [smallPrepared, state_simp_rules]
  · intro address outside
    rw [smallPrepared_memory]

@[simp] theorem smallPrepared_pc (s : ArmState) (base : BitVec 64) :
    read_pc (smallPrepared s base) = base + 964#64 := by simp [smallPrepared, state_simp_rules]

theorem smallPrepared_data (s : ArmState) (base : BitVec 64) (word : BitVec 64) (index size : Nat)
    (bounded : size < 2^64) (inside : index < size)
    (number : r (.GPR 8#5) s = word)
    (bitCounter : r (.GPR 9#5) s = BitVec.ofNat 64 (8 * index))
    (byteCounter : r (.GPR 10#5) s = BitVec.ofNat 64 index)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size) :
    r (.GPR 9#5) (smallPrepared s base) = BitVec.ofNat 64 (8 * (index + 1)) ∧
    r (.GPR 11#5) (smallPrepared s base) = BitVec.ofNat 64 (index + 1) ∧
    r (.GPR 12#5) (smallPrepared s base) = emittedWord (.small word) index >>> (8 * (index % 8)) ∧
    (r (.FLAG .Z) (smallPrepared s base) = 1#1 ↔ index + 1 = size) := by
  have indexBound : index < 2^64 := by omega
  have afterBound : index + 1 < 2^64 := by omega
  have increment : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by bv_omega
  have bitsIncrement : BitVec.ofNat 64 (8 * index) + 8#64 = BitVec.ofNat 64 (8 * (index + 1)) := by bv_omega
  have wordEq : (if 8 ≤ (BitVec.ofNat 64 index).toNat then 0#64 else word) =
      emittedWord (.small word) index := by
    rw [emittedWord_small, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound]
    by_cases low : index < 8 <;> simp [low, show 8 ≤ index ↔ ¬ index < 8 by omega]
  have same : BitVec.ofNat 64 size = BitVec.ofNat 64 (index + 1) ↔ index + 1 = size := by
    constructor
    · intro equal
      have natEqual := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt afterBound] at natEqual
      omega
    · intro equal
      rw [equal]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) [smallPrepared, state_simp_rules, bitCounter, bitsIncrement]
  · simp (config := {decide := true}) [smallPrepared, state_simp_rules, byteCounter, increment]
  · simp (config := {decide := true}) only [smallPrepared, state_simp_rules, number, bitCounter,
      byteCounter, byte_shift_count, wordEq]
  · simpa (config := {decide := true}) [smallPrepared, state_simp_rules, length, byteCounter,
      increment, Udivti3.cmp_zero] using same

end SszArm.Emit.Uint
