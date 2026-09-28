import SszArm.MeasureResultLower

namespace SszArm.Measure.Result

open Delimited (MemoryFrame Protected)

def Payload.bytes : Payload → Nat
  | .word => 8
  | .pair => 16
  | .status => 4

theorem Payload.frame (kind : Payload) (s : ArmState) (address low high : BitVec 64)
    (bound : address.toNat + kind.bytes ≤ 2^64) :
    MemoryFrame [(address.toNat, kind.bytes)] s (kind.store s address low high) := by
  intro a outside
  have apart := outside (address.toNat, kind.bytes) (by simp)
  cases kind with
  | word => exact BoolCodec.write_mem_bytes_frame s address 8 low a bound apart
  | status => exact BoolCodec.write_mem_bytes_frame s address 4 (low.setWidth 32) a bound apart
  | pair =>
    change address.toNat + 16 ≤ 2^64 at bound
    have position : (address + 8#64).toNat = address.toNat + 8 := by bv_omega
    change a.toNat < address.toNat ∨ address.toNat + 16 ≤ a.toNat at apart
    unfold store
    rw [BoolCodec.write_mem_bytes_frame _ _ 8 high a (by rw [position]; omega)
      (by rw [position]; omega),
      BoolCodec.write_mem_bytes_frame s address 8 low a (by omega) (by omega)]

theorem savedPair_read_low (s : ArmState) (tmp : BitVec 5)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (savedPair s tmp) = r (.GPR 9#5) s := by
  unfold savedPair
  rw [BoolCodec.read_mem_bytes_write_mem_bytes_disjoint _ 8 8 _ _ _
    (by bv_omega) (by bv_omega) (by bv_omega),
    BoolCodec.read_mem_bytes_write_mem_bytes_same s 8 _ _ (by bv_omega)]

theorem savedPair_read_high (s : ArmState) (tmp : BitVec 5)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat) :
    read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (savedPair s tmp) = r (.GPR tmp) s := by
  exact BoolCodec.read_mem_bytes_write_mem_bytes_same _ 8 _ _ (by bv_omega)

theorem Lower.restored (kind : Lower) (s : ArmState) (base : BitVec 64)
    (stack : 16 ≤ (r (.GPR 31#5) s).toNat)
    (bound : (r (.GPR 19#5) s + kind.offset).toNat + kind.kind.bytes ≤ 2^64)
    (apart : Protected [((r (.GPR 19#5) s + kind.offset).toNat, kind.kind.bytes)]
      (r (.GPR 31#5) s - 16#64).toNat 16) :
    kind.result s base = w .PC (base + BitVec.ofNat 64 kind.finish) (kind.memory s) := by
  have frame := kind.kind.frame (savedPair s kind.tmp)
    (r (.GPR 19#5) s + kind.offset) (kind.low s) (kind.high s) bound
  have low : read_mem_bytes 8 (r (.GPR 31#5) s - 16#64) (kind.memory s) = r (.GPR 9#5) s := by
    exact (frame.read _ 8 (by bv_omega) (by simpa using apart.subspan 0 8 (by decide))).trans
      (savedPair_read_low s kind.tmp stack)
  have high : read_mem_bytes 8 (r (.GPR 31#5) s - 8#64) (kind.memory s) = r (.GPR kind.tmp) s := by
    have position : (r (.GPR 31#5) s - 8#64).toNat =
        (r (.GPR 31#5) s - 16#64).toNat + 8 := by bv_omega
    exact (frame.read _ 8 (by bv_omega) (by rw [position]; exact apart.subspan 8 8 (by decide))).trans
      (savedPair_read_high s kind.tmp stack)
  unfold Lower.result
  dsimp only
  rw [low, high]
  have registers : ∀ reg, r (.GPR reg) (kind.memory s) = r (.GPR reg) s := by
    intro reg
    cases kind <;> simp [Lower.memory, Lower.kind, Lower.low, Lower.high, Payload.store,
      savedPair, state_simp_rules]
  congr 1
  apply state_eq_iff_components_eq.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro field
    cases field with
    | GPR reg =>
      by_cases nine : reg = 9#5 <;> by_cases temporary : reg = kind.tmp <;>
        (try subst reg) <;> simp_all [NatExact.r_gpr_w, state_simp_rules]
    | PC => simp [state_simp_rules]
    | SFP reg => simp [state_simp_rules]
    | FLAG flag => simp [state_simp_rules]
    | ERR => simp [state_simp_rules]
  · simp [state_simp_rules]
  · intro n address; simp [state_simp_rules]

@[simp] theorem Lower.program (kind : Lower) (s : ArmState) (base : BitVec 64) :
    (kind.result s base).program = s.program := by
  cases kind <;> simp [Lower.result, Lower.memory, Lower.kind, Payload.store, savedPair, state_simp_rules]

@[simp] theorem Lower.error (kind : Lower) (s : ArmState) (base : BitVec 64) :
    read_err (kind.result s base) = read_err s := by
  cases kind <;> simp [Lower.result, Lower.memory, Lower.kind, Payload.store, savedPair, state_simp_rules]

@[simp] theorem Lower.pc (kind : Lower) (s : ArmState) (base : BitVec 64) :
    read_pc (kind.result s base) = base + BitVec.ofNat 64 kind.finish := by
  simp [Lower.result, state_simp_rules]

@[simp] theorem Lower.sp (kind : Lower) (s : ArmState) (base : BitVec 64) :
    r (.GPR 31#5) (kind.result s base) = r (.GPR 31#5) s := by
  cases kind <;> simp (config := {decide := true})
    [Lower.result, Lower.memory, Lower.kind, Lower.tmp, Payload.store, savedPair, state_simp_rules]

@[simp] theorem Lower.vector (kind : Lower) (s : ArmState) (base : BitVec 64) (reg : BitVec 5) :
    r (.SFP reg) (kind.result s base) = r (.SFP reg) s := by
  cases kind <;> simp [Lower.result, Lower.memory, Lower.kind, Payload.store, savedPair, state_simp_rules]

theorem Lower.register (kind : Lower) (s : ArmState) (base : BitVec 64) (reg : BitVec 5)
    (nine : reg ≠ 9#5) (temporary : reg ≠ kind.tmp) :
    r (.GPR reg) (kind.result s base) = r (.GPR reg) s := by
  cases kind <;> simp_all [Lower.result, Lower.memory, Lower.kind, Lower.tmp,
    Payload.store, savedPair, NatExact.r_gpr_w, state_simp_rules]

end SszArm.Measure.Result
