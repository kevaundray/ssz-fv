import SszArm.EmitUintLoopLargeSelect

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def largePrepareOps : List ByteOp := [.p1076, .p1080, .p1084, .p1088, .p1092]

@[irreducible] def largePrepared (s : ArmState) (base : BitVec 64) : ArmState :=
  let shift := r (.GPR 10#5) s &&& 56#64
  w .PC (base + 1096#64)
    (w (.GPR 10#5) (r (.GPR 10#5) s + 8#64)
      (w (.GPR 12#5) (r (.GPR 12#5) s >>> (shift.toNat % 64))
        (w (.GPR 13#5) (r (.GPR 11#5) s + 1#64)
          (w (.GPR 14#5) shift
            (write_pstate (AddWithCarry (r (.GPR 1#5) s) (~~~(r (.GPR 11#5) s + 1#64)) 1#1).2 s)))))

theorem large_prepare_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1076#64) : run 5 s = largePrepared s base := by
  have position : r .PC s = base + 1076#64 := pc
  have follows : ByteFollows base largePrepareOps s := by
    simp [largePrepareOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next,
      Dispatch.next, state_simp_rules, position, BitVec.add_assoc]
  rw [show 5 = largePrepareOps.length by rfl, byte_run base largePrepareOps s code error aligned follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases h10 : reg = 10#5
      · subst reg
        simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
          position, BitVec.add_assoc]
      · by_cases h12 : reg = 12#5
        · subst reg
          simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
            put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
            position, BitVec.add_assoc]
        · by_cases h13 : reg = 13#5
          · subst reg
            simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
              put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
              position, BitVec.add_assoc]
          · by_cases h14 : reg = 14#5
            · subst reg
              simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
                put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
                position, BitVec.add_assoc]
            · simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
                put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
                NatExact.r_gpr_w, h10, h12, h13, h14, position, BitVec.add_assoc]
    | FLAG flag =>
      cases flag <;>
        simp (config := {decide := true}) [byteBlock, largePrepareOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, largePrepared, state_simp_rules,
          position, BitVec.add_assoc]
    | PC =>
      simp [byteBlock, largePrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, largePrepared, state_simp_rules, position, BitVec.add_assoc]
    | SFP reg =>
      simp [byteBlock, largePrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, largePrepared, state_simp_rules]
    | ERR =>
      simp [byteBlock, largePrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
        Dispatch.next, largePrepared, state_simp_rules]
  · simp [byteBlock, largePrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
      Dispatch.next, largePrepared, state_simp_rules]
  · intro bytes address
    simp [byteBlock, largePrepareOps, ByteOp.effect, put, next, Dispatch.compare64,
      Dispatch.next, largePrepared, state_simp_rules]

@[simp] theorem largePrepared_memory (s : ArmState) (base : BitVec 64) :
    (largePrepared s base).mem = s.mem := by simp [largePrepared, state_simp_rules]

@[simp] theorem largePrepared_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (untouched : reg ∉ [10#5, 12#5, 13#5, 14#5]) :
    r (.GPR reg) (largePrepared s base) = r (.GPR reg) s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at untouched
  simp [largePrepared, state_simp_rules, untouched.1, untouched.2.1,
    untouched.2.2.1, untouched.2.2.2]

theorem largePrepared_frame (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) :
    Frame s (largePrepared s base) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [largePrepared, state_simp_rules]
  · simp [largePrepared, state_simp_rules]
  · intro reg outside
    apply largePrepared_register
    simp_all
  · intro reg
    simp [largePrepared, state_simp_rules]
  · intro address outside
    rw [largePrepared_memory]

@[simp] theorem largePrepared_pc (s : ArmState) (base : BitVec 64) :
    read_pc (largePrepared s base) = base + 1096#64 := by simp [largePrepared, state_simp_rules]

theorem largePrepared_data (s : ArmState) (base : BitVec 64) (word : BitVec 64) (index size : Nat)
    (bounded : size < 2^64) (inside : index < size)
    (number : r (.GPR 12#5) s = word)
    (bitCounter : r (.GPR 10#5) s = BitVec.ofNat 64 (8 * index))
    (byteCounter : r (.GPR 11#5) s = BitVec.ofNat 64 index)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size) :
    r (.GPR 10#5) (largePrepared s base) = BitVec.ofNat 64 (8 * (index + 1)) ∧
    r (.GPR 13#5) (largePrepared s base) = BitVec.ofNat 64 (index + 1) ∧
    r (.GPR 12#5) (largePrepared s base) = word >>> (8 * (index % 8)) ∧
    (r (.FLAG .Z) (largePrepared s base) = 1#1 ↔ index + 1 = size) := by
  have afterBound : index + 1 < 2^64 := by omega
  have increment : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by bv_omega
  have bitsIncrement : BitVec.ofNat 64 (8 * index) + 8#64 = BitVec.ofNat 64 (8 * (index + 1)) := by bv_omega
  have same : BitVec.ofNat 64 size = BitVec.ofNat 64 (index + 1) ↔ index + 1 = size := by
    constructor
    · intro equal
      have natEqual := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt afterBound] at natEqual
      omega
    · intro equal
      rw [equal]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [largePrepared, state_simp_rules, bitCounter, bitsIncrement]
  · simp [largePrepared, state_simp_rules, byteCounter, increment]
  · simp (config := {decide := true}) only [largePrepared, state_simp_rules,
      number, bitCounter, byte_shift_count]
  · simpa (config := {decide := true}) [largePrepared, state_simp_rules, length,
      byteCounter, increment, Udivti3.cmp_zero] using same

end SszArm.Emit.Uint
