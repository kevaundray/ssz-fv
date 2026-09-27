import SszX86.NatAddReserveLarge
import SszX86.NatAddReserveSmall

namespace SszX86.NatAdd.Reservation

/-- The small-overflow reservation either exits without a memory change or
commits exactly the cursor and `[low, 1]`, before publishing the result pair. -/
theorem small_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Small.Header s address capacity used)
    (hm : UintCodec.Large.Mapped s.dmem address capacity.toNat)
    (P : MachineState → Prop)
    (hp : ∀ t, Small.Post s base address capacity used t → Eventually (step e) P t) :
    Eventually (step e) P (s, base + 676) :=
  eventually_trans (step e) _ P _ (Small.runs e base hc s address capacity used header hm) hp

/-- The entire actual large-branch reservation from the two significant counts.
Count+1 overflow reaches1399; reserve failure reaches766 without writing memory;
success reaches536 with the exact reservation registers and only the cursor store. -/
theorem large_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (address capacity used : BitVec 64)
    (header : Large.Header s address capacity used)
    (P : MachineState → Prop)
    (overflow : max s.regs.rax.toNat s.regs.r11.toNat = 2^64 - 1 →
      ∀ flags, Eventually (step e) P (Large.maxState s flags, base + 1399))
    (reserved : max s.regs.rax.toNat s.regs.r11.toNat ≠ 2^64 - 1 →
      ∀ flags t, Large.Post (Large.maxState s flags) base address capacity used t →
        Eventually (step e) P t) :
    Eventually (step e) P (s, base + 397) := by
  apply Large.max_cps e base hc
  intro flags
  by_cases h : max s.regs.rax.toNat s.regs.r11.toNat = 2^64 - 1
  · rw [ite_eq_left h]
    exact overflow h flags
  · rw [ite_eq_right h]
    exact eventually_trans (step e) _ P _
      (Large.runs e base hc (Large.maxState s flags) address capacity used
        ⟨header.address_load, header.capacity_load, header.used_load⟩)
      (reserved h flags)

end SszX86.NatAdd.Reservation
