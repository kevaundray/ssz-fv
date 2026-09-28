import SszX86.BitVectorMapping

namespace SszX86.BitVector.Mapping

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem undefined_lift {α : Type} [NondetSupportingType α] (ret : α → Effects)
    (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value).All P → (ret value).All Q) :
    (Effects.undefined ret).All P → (Effects.undefined ret).All Q := by
  intro h value
  exact hret value (h value)

/-- Generic scalar instruction preservation, derived from the pinned interpreter.
The premise is successful Effects.All, not an independent execution oracle. -/
theorem operation_lift [Labels] [AddressSize] {w : Width} (op : Operation w)
    (s : MachineData) (p : Std.Rco Int64) (next : MachineData → Effects)
    (jump : Int64 → MachineData → Effects) (P Q : MachineState → Prop)
    (before : DataMem) (hdom : Extends before s.dmem)
    (hnext : ∀ t, Extends before t.dmem → (next t).All P → (next t).All Q)
    (hjump : ∀ pc t, Extends before t.dmem → (jump pc t).All P → (jump pc t).All Q) :
    (op.interp p s next jump).All P → (op.interp p s next jump).All Q := by
  cases op <;> simp only [Operation.interp, Reg.interp]
  case bswap dst =>
    cases w with
    | W8 => exact @undefined_lift _ (.bitvec .W8) _ P Q (fun _ => hnext _ hdom)
    | W16 => exact @undefined_lift _ (.bitvec .W16) _ P Q (fun _ => hnext _ hdom)
    | W32 => exact hnext _ hdom
    | W64 => exact hnext _ hdom
  all_goals
    repeat' first
    | (apply hnext; assumption)
    | (apply hjump; assumption)
    | (apply hnext; exact hdom.trans (Extends.store _ _ _ _))
    | (apply hjump; exact hdom.trans (Extends.store _ _ _ _))
    | (apply operand_lift; intro value)
    | (apply regmem_lift; intro value)
    | (apply relative_lift; intro value)
    | (apply load_lift; intro value)
    | (apply set_lift (before := before) <;> first | assumption | (intro t ht))
    | apply store_lift
    | (apply undefined_lift; intro value)
    | split

end SszX86.BitVector.Mapping
