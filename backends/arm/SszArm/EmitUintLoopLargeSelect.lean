import SszArm.EmitUintLoopLargeLoad

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def largeSelectOps : List ByteOp := [.p1132, .p1136, .p1140]

@[irreducible] def largeSelected (s : ArmState) (base : BitVec 64) : ArmState :=
  let index := r (.GPR 11#5) s >>> 3
  w .PC (if (r (.GPR 8#5) s).toNat ≤ index.toNat then base + 1072#64 else base + 1144#64)
    (w (.GPR 12#5) index (write_pstate (AddWithCarry index (~~~r (.GPR 8#5) s) 1#1).2 s))

theorem large_select_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1132#64) : run 3 s = largeSelected s base := by
  have position : r .PC s = base + 1132#64 := pc
  have follows : ByteFollows base largeSelectOps s := by
    simp [largeSelectOps, ByteFollows, ByteOp.row, ByteOp.effect, put, next,
      Dispatch.compare64, Dispatch.next, state_simp_rules, position, BitVec.add_assoc]
  rw [show 3 = largeSelectOps.length by rfl, byte_run base largeSelectOps s code error aligned follows]
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases written : reg = 12#5
      · subst reg
        simp (config := {decide := true}) [byteBlock, largeSelectOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, largeSelected,
          state_simp_rules, Udivti3.cmp_carry]
      · simp (config := {decide := true}) [byteBlock, largeSelectOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, largeSelected,
          state_simp_rules, NatExact.r_gpr_w, written, Udivti3.cmp_carry]
    | FLAG flag =>
      cases flag <;>
        simp (config := {decide := true}) [byteBlock, largeSelectOps, ByteOp.effect,
          put, next, Dispatch.compare64, Dispatch.next, largeSelected,
          state_simp_rules, Udivti3.cmp_carry]
    | PC =>
      simp [byteBlock, largeSelectOps, ByteOp.effect, put, next,
        Dispatch.compare64, Dispatch.next, largeSelected, state_simp_rules, Udivti3.cmp_carry]
    | SFP reg =>
      simp [byteBlock, largeSelectOps, ByteOp.effect, put, next,
        Dispatch.compare64, Dispatch.next, largeSelected, state_simp_rules]
    | ERR =>
      simp [byteBlock, largeSelectOps, ByteOp.effect, put, next,
        Dispatch.compare64, Dispatch.next, largeSelected, state_simp_rules]
  · simp [byteBlock, largeSelectOps, ByteOp.effect, put, next,
      Dispatch.compare64, Dispatch.next, largeSelected, state_simp_rules]
  · intro bytes address
    simp [byteBlock, largeSelectOps, ByteOp.effect, put, next,
      Dispatch.compare64, Dispatch.next, largeSelected, state_simp_rules]

@[simp] theorem largeSelected_memory (s : ArmState) (base : BitVec 64) :
    (largeSelected s base).mem = s.mem := by simp [largeSelected, state_simp_rules]

@[simp] theorem largeSelected_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (different : reg ≠ 12#5) :
    r (.GPR reg) (largeSelected s base) = r (.GPR reg) s := by
  simp [largeSelected, state_simp_rules, different]

theorem largeSelected_frame (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) :
    Frame s (largeSelected s base) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [largeSelected, state_simp_rules]
  · simp [largeSelected, state_simp_rules]
  · intro reg outside
    exact largeSelected_register s base reg (by simp_all)
  · intro reg
    simp [largeSelected, state_simp_rules]
  · intro address outside
    rw [largeSelected_memory]

theorem largeSelected_data (s : ArmState) (base : BitVec 64) (index count : Nat)
    (indexBound : index < 2^64) (countBound : count < 2^64)
    (counter : r (.GPR 11#5) s = BitVec.ofNat 64 index)
    (length : r (.GPR 8#5) s = BitVec.ofNat 64 count) :
    r (.GPR 12#5) (largeSelected s base) = BitVec.ofNat 64 (index / 8) ∧
    read_pc (largeSelected s base) =
      if index / 8 < count then base + 1144#64 else base + 1072#64 := by
  have shift : (BitVec.ofNat 64 index >>> 3) = BitVec.ofNat 64 (index / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound,
      Nat.shiftRight_eq_div_pow]
    omega
  have quotientBound : index / 8 < 2^64 := by omega
  simp only [largeSelected, state_simp_rules, counter, length, shift, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt countBound, Nat.mod_eq_of_lt quotientBound]
  constructor
  · simp (config := {decide := true}) [state_simp_rules]
  · by_cases inside : index / 8 < count <;> simp [inside, show count ≤ index / 8 ↔ ¬index / 8 < count by omega]

@[irreducible] def zeroWordLoaded (s : ArmState) (base : BitVec 64) : ArmState :=
  w .PC (base + 1076#64) (w (.GPR 12#5) 0#64 s)

theorem zero_word_run (s : ArmState) (base : BitVec 64)
    (code : CodeAt s base) (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (pc : read_pc s = base + 1072#64) : run 1 s = zeroWordLoaded s base := by
  change stepi s = _
  rw [byte_step s base .p1072 code pc error aligned]
  change r .PC s = _ at pc
  simp [ByteOp.effect, put, next, Dispatch.next, zeroWordLoaded, state_simp_rules, pc, BitVec.add_assoc]
  exact w_of_w_commute (by decide)

@[simp] theorem zeroWordLoaded_memory (s : ArmState) (base : BitVec 64) :
    (zeroWordLoaded s base).mem = s.mem := by simp [zeroWordLoaded, state_simp_rules]

@[simp] theorem zeroWordLoaded_register (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (different : reg ≠ 12#5) :
    r (.GPR reg) (zeroWordLoaded s base) = r (.GPR reg) s := by
  simp [zeroWordLoaded, state_simp_rules, different]

@[simp] theorem zeroWordLoaded_word (s : ArmState) (base : BitVec 64) :
    r (.GPR 12#5) (zeroWordLoaded s base) = 0#64 := by simp [zeroWordLoaded, state_simp_rules]

@[simp] theorem zeroWordLoaded_pc (s : ArmState) (base : BitVec 64) :
    read_pc (zeroWordLoaded s base) = base + 1076#64 := by simp [zeroWordLoaded, state_simp_rules]

theorem zeroWordLoaded_frame (s : ArmState) (base : BitVec 64) (args : Args) (size : Nat) :
    Frame s (zeroWordLoaded s base) args size := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [zeroWordLoaded, state_simp_rules]
  · simp [zeroWordLoaded, state_simp_rules]
  · intro reg outside
    exact zeroWordLoaded_register s base reg (by simp_all)
  · intro reg
    simp [zeroWordLoaded, state_simp_rules]
  · intro address outside
    rw [zeroWordLoaded_memory]

end SszArm.Emit.Uint
