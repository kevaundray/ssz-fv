import SszArm.EmitUintWidth

namespace SszArm.Emit.Uint

open SszNative (NatOperand)

def capacityOps : List WidthOp := [.p904, .p908, .p912]

theorem capacity_guard (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 904#64)
    (length : r (.GPR 1#5) s = BitVec.ofNat 64 size) :
    ∃ t, run 3 s = t ∧ Frame s t args size ∧
      read_pc t = base + (if size = 0 then 1000#64 else 916#64) ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size := by
  have within : (r (.GPR 1#5) s).toNat ≤ (r (.GPR 21#5) s).toNat := by
    rw [length, registers.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt owned.representable]
    exact owned.fitting
  have zero : r (.GPR 1#5) s = 0#64 ↔ size = 0 := by
    rw [length]
    have bound := owned.representable
    bv_omega
  have follows : WidthFollows base capacityOps s := by
    change r .PC s = base + 904#64 at pc
    simp [capacityOps, WidthFollows, WidthOp.row, WidthOp.effect,
      Dispatch.next, Dispatch.compare64, state_simp_rules, pc, BitVec.add_assoc]
    intro carry
    apply BitVec.eq_of_toNat_eq
    have reverse := (Udivti3.cmp_carry _ _).mp carry
    omega
  let t := widthBlock base capacityOps s
  refine ⟨t, width_run base capacityOps s code error aligned follows,
    width_readonly_frame base capacityOps s args size (by decide), ?_, ?_⟩
  · simp [t, capacityOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      Dispatch.compare64, state_simp_rules, zero, apply_ite]
  · simpa [t, capacityOps, widthBlock, WidthOp.effect, put, next, Dispatch.next,
      Dispatch.compare64, state_simp_rules] using length

/-- The whole real width prefix derives both representability and capacity
branch safety from the original logical call and physical observations. -/
theorem width_prefix (s : ArmState) (base : BitVec 64) (args : Args)
    (width number : NatOperand) (size : Nat)
    (code : CodeAt s base) (owned : Owned s args (.uint width) (.uint number) size)
    (registers : BodyRegisters s args) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 60#64)
    (descriptor : r (.GPR 1#5) s = args.descriptor) (tag : r (.GPR 9#5) s = 1#64) :
    ∃ fuel t, run fuel s = t ∧ Frame s t args size ∧
      read_pc t = base + (if size = 0 then 1000#64 else 916#64) ∧
      r (.GPR 1#5) t = BitVec.ofNat 64 size := by
  obtain ⟨fuel, u, runWidth, frame, exit, length⟩ :=
    width_normalize s base args width number size code owned registers error aligned pc descriptor tag
  rcases exit with capacity | ⟨empty, zero⟩
  · obtain ⟨t, runGuard, guardFrame, exit, value⟩ := capacity_guard u base args width number size
      (frame.code code) (frame.owned owned) (frame.bodyRegisters registers)
      (frame.error.trans error) (frame.aligned aligned) capacity length
    refine ⟨fuel + 3, t, ?_, frame.trans guardFrame, exit, value⟩
    rw [run_plus, runWidth, runGuard]
  · exact ⟨fuel, u, runWidth, frame, by simpa [zero] using empty, length⟩

end SszArm.Emit.Uint
