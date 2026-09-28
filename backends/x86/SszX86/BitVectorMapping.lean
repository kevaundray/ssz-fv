import SszX86.BitVectorCore

namespace SszX86.BitVector.Mapping
open UintCodec

/-- Safe native instructions may change bytes, but never destroy a mapping. -/
def Extends (before after : DataMem) : Prop :=
  ∀ p n, Large.Mapped before p n → Large.Mapped after p n

theorem Extends.refl (m : DataMem) : Extends m m := fun _ _ h => h

theorem Extends.trans {a b c : DataMem} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := fun p n h => hbc p n (hab p n h)

theorem Extends.store (m : DataMem) (address : BitVec 64) (count : Nat) (value : Int) :
    Extends m (Mem.storeInt m address count value) := by
  intro p n h
  exact Large.mapped_store _ _ _ _ _ _ h

/-- MMIO is rejected by Effects.All, so a successful load retains its input state. -/
theorem load_lift (s : MachineData) (address : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (s.load address w ret).All P → (s.load address w ret).All Q := by
  unfold MachineData.load
  cases read : Mem.loadInt s.dmem address w.bytes <;>
    simp only [Effects.All]
  · exact False.elim
  · exact hret _

theorem store_lift (s : MachineData) (address : BitVec 64) {w : Width}
    (value : w.type) (ret : MachineData → Effects) (P Q : MachineState → Prop)
    (hret : (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All P →
      (ret {s with dmem := Mem.storeInt s.dmem address w.bytes value.toInt}).All Q) :
    (s.store address value ret).All P → (s.store address value ret).All Q := by
  unfold MachineData.store
  cases read : Mem.loadInt s.dmem address w.bytes <;>
    simp only [Effects.All]
  · exact False.elim
  · exact hret

theorem regmem_lift [Labels] [AddressSize] {w : Width} (o : RegOrMem w)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (o.interp s p ret).All P → (o.interp s p ret).All Q := by
  cases o with
  | reg r => exact hret _
  | mem a => exact load_lift s _ w ret P Q hret

theorem operand_lift [Labels] [AddressSize] {w : Width} (o : Operand w)
    (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects)
    (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (o.interp s p ret).All P → (o.interp s p ret).All Q := by
  cases o with
  | regOrMem rm => exact regmem_lift rm s p ret P Q hret
  | imm value => exact hret _

theorem relative_lift [Labels] [AddressSize] (o : RelRegOrMem)
    (s : MachineData) (p : Std.Rco Int64) (ret : BitVec 64 → MachineData → Effects)
    (P Q : MachineState → Prop)
    (hret : ∀ value, (ret value s).All P → (ret value s).All Q) :
    (o.interp s p ret).All P → (o.interp s p ret).All Q := by
  cases o with
  | rel value => exact hret _
  | reg r => exact hret _
  | mem a => exact load_lift s _ .W64 ret P Q hret

theorem set_lift [Labels] [AddressSize] {w : Width} (dst : Dst w)
    (s : MachineData) (p : Std.Rco Int64) (value : w.type)
    (ret : MachineData → Effects) (P Q : MachineState → Prop) (before : DataMem)
    (hdom : Extends before s.dmem)
    (hret : ∀ t, Extends before t.dmem → (ret t).All P → (ret t).All Q) :
    (s.set dst value p ret).All P → (s.set dst value p ret).All Q := by
  cases dst with
  | reg r => exact hret _ hdom
  | mem a =>
    apply store_lift
    exact hret _ (hdom.trans (Extends.store _ _ _ _))

end SszX86.BitVector.Mapping
