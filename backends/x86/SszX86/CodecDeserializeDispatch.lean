import SszX86.CodecDeserializeTable
import SszX86.DispatchJump

set_option autoImplicit false

namespace SszX86.CodecDeserialize
open SszNative UintCodec

/-- Setup changes only the same registers as the original native prologue. -/
def tagState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat tag}}

def prepared (s : MachineData) (desc : SszNative.Codec.Desc) : MachineData :=
  tagState (Dispatch.abiState (Dispatch.stackState (Dispatch.savedState s)))
    (Codec.descTag desc)

def offsetState (s : MachineData) (tag : Nat) : MachineData :=
  {s with regs := {s.regs with rax := UInt64.ofNat (106520 + dispatchEntry tag)}}

def bodyState (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc) : MachineData :=
  Dispatch.addState (offsetState (Dispatch.tableState (prepared s desc) base) (Codec.descTag desc))

private theorem tag_runs (e : Executable) (base : Int64) (hc : Dispatch.CodeAt e base)
    (s : MachineData) (desc : SszNative.Codec.Desc) (P : MachineState → Prop)
    (tag : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (Codec.descTag desc : Int))
    (next : Eventually (BoolCodec.step e) P (tagState s (Codec.descTag desc), base + 29)) :
    Eventually (BoolCodec.step e) P (s, base + 26) := by
  dispatch_step 10 using hc
  cases desc with
  | primitive shape =>
    cases shape <;>
      simpa [MachineData.load, Effects.All, tag, tagState, Codec.descTag, Emit.descTag] using next
  | _ => simpa [MachineData.load, Effects.All, tag, tagState, Codec.descTag] using next

private theorem offset_runs (e : Executable) (base : Int64) (hc : Dispatch.CodeAt e base)
    (s : MachineData) (tag : Nat) (bound : tag < 13) (P : MachineState → Prop)
    (tagged : s.regs.rax = UInt64.ofNat tag)
    (address : s.regs.rcx.toBitVec = Dispatch.tableAddress base)
    (table : Dispatch.TableAt s.dmem base)
    (next : Eventually (BoolCodec.step e) P (offsetState s tag, base + 40)) :
    Eventually (BoolCodec.step e) P (s, base + 36) := by
  have loaded := table_load s.dmem base table tag bound
  have indexed : BitVec.ofInt 64 (s.regs.rcx.toBitVec.toInt + s.regs.rax.toBitVec.toInt * 4) =
      Dispatch.tableAddress base + BitVec.ofNat 64 (4 * tag) := by
    rw [BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
      address, tagged, UInt64.toBitVec_ofNat', BitVec.ofNat_mul]
    congr 1
    change BitVec.ofNat 64 tag * 4#64 = 4#64 * BitVec.ofNat 64 tag
    exact BitVec.mul_comm _ _
  have register (n : Nat) : ({toBitVec := BitVec.ofNat 64 n} : UInt64) = UInt64.ofNat n := by
    apply UInt64.toBitVec_inj.1
    rfl
  dispatch_step 12 using hc
  simpa only [MachineData.load, Effects.All, indexed, loaded, table_signed tag bound,
    offsetState, UInt64.toBitVec_ofNat', register] using next

/-- Actual entry-to-indirect-target execution for every raw descriptor. The
only mutable region so far consists of the six saved register words. -/
theorem dispatch_runs (e : Executable) (base : Int64) (hc : Dispatch.CodeAt e base)
    (s : MachineData) (desc : SszNative.Codec.Desc) (readable : Codec.Footprint)
    (descriptor : Codec.DescAt s.dmem readable s.regs.rsi.toBitVec desc)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (apart : ∀ i < 8, ∀ j < 48,
      s.regs.rsi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (table : Dispatch.TableAt s.dmem base)
    (tableApart : ∀ i < Dispatch.tableBytes.length, ∀ j < 48,
      Dispatch.tableAddress base + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j) :
    Eventually (BoolCodec.step e) (fun t =>
      t = (bodyState s base desc, base + Int64.ofNat (dispatchEntry (Codec.descTag desc))))
      (s, base) := by
  apply Dispatch.pushes_runs e base hc s _ stack
  apply Dispatch.stack_runs e base hc
  apply Dispatch.abi_runs e base hc
  apply tag_runs e base hc _ desc
  · change Mem.loadInt (Dispatch.savedMem s) s.regs.rsi.toBitVec 8 = _
    rw [Dispatch.saved_load s _ 8 apart]
    exact descriptor.tag
  apply Dispatch.lea_runs e base hc
  apply offset_runs e base hc _ (Codec.descTag desc) (descTag_bound desc) _ rfl rfl
  · exact Dispatch.saved_table s base table tableApart
  apply Dispatch.add_runs e base hc
  apply Dispatch.indirect_runs e base hc
  apply Eventually.done
  simp only [bodyState, prepared, Dispatch.addState, offsetState, Dispatch.tableState,
    UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofNat', table_target, Int64.ofBitVec_toBitVec]

@[simp] theorem body_memory (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc) :
    (bodyState s base desc).dmem = Dispatch.savedMem s := rfl

@[simp] theorem body_sp (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc) :
    (bodyState s base desc).regs.rsp.toBitVec = s.regs.rsp.toBitVec - 360 := by
  simp only [bodyState, Dispatch.addState, offsetState, Dispatch.tableState, prepared,
    tagState, Dispatch.abiState, Dispatch.stackState, Dispatch.savedState,
    UInt64.toBitVec_ofBitVec]
  bv_omega

end SszX86.CodecDeserialize
