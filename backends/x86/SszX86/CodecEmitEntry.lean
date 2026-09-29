import SszX86.EmitRoute
import SszX86.CodecStack

set_option autoImplicit false

namespace SszX86.CodecEmit
open SszNative UintCodec

def tableEntryState (s : MachineData) (base : Int64) (descriptor : BitVec 64)
    (kind : Emit.TableKind) : MachineData :=
  Emit.routed (Emit.prepared s descriptor (BitVec.ofNat 8 (kind.index + 2))) base kind

/-- The existing four-way Value table includes the real Seq and Union entries.
This executes the six PUSHes, ABI setup, both scalar exclusions and indirect JMP;
the destination is derived from immutable table bytes, not assumed reachable. -/
theorem table_entry_runs (e : Executable) (base : Int64) (code : Emit.CodeAt e base)
    (s : MachineData) (descriptor : BitVec 64) (kind : Emit.TableKind)
    (stack : Large.Mapped s.dmem (s.regs.rsp.toBitVec - 48) 48)
    (descLoad : Mem.loadInt s.dmem s.regs.rsi.toBitVec 8 = some (descriptor.toNat : Int))
    (valueLoad : Mem.loadInt s.dmem s.regs.rdx.toBitVec 1 =
      some ((BitVec.ofNat 8 (kind.index + 2)).toNat : Int))
    (descApart : ∀ i < 8, ∀ j < 48,
      s.regs.rsi.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (valueApart : ∀ i < 1, ∀ j < 48,
      s.regs.rdx.toBitVec + BitVec.ofNat 64 i ≠
        s.regs.rsp.toBitVec - 48 + BitVec.ofNat 64 j)
    (nonzero : descriptor ≠ 0#64) (notOne : descriptor.take 32 ≠ 1#32)
    (table : Emit.TableAt s.dmem base)
    (tableApart : ∀ a, Emit.InSpan a (Emit.tableAddress base) 16 →
      ¬ SszX86.Codec.StackWrites s.regs.rsp.toBitVec 48 a) :
    Eventually (Emit.step e)
      (fun final => final = (tableEntryState s base descriptor kind,
        base + Int64.ofNat kind.entry)) (s, base) := by
  have savedTable : Emit.TableAt (Emit.savedMem s) base := by
    intro i hi
    rw [SszX86.Codec.savedSix_frame s 48 (by decide) _
      (tableApart _ ⟨i, by simpa only [Emit.tableBytes, List.length_cons, List.length_nil] using hi,
        rfl⟩)]
    exact table i hi
  apply Emit.setup_runs e base code s descriptor (BitVec.ofNat 8 (kind.index + 2))
    _ stack descLoad valueLoad descApart valueApart
  apply Emit.select_table e base code _ kind _ nonzero notOne
  · cases kind <;> rfl
  · exact savedTable
  · exact Eventually.done _ rfl

/-- Root anchors are retained through the actual indirect dispatch. In
particular RCX's original Option<Plan> pointer is now R8, not a synthetic plan. -/
theorem tableEntryState_anchors (s : MachineData) (base : Int64)
    (descriptor : BitVec 64) (kind : Emit.TableKind) :
    Emit.AtBody s (tableEntryState s base descriptor kind) ∧
      (tableEntryState s base descriptor kind).regs.r8 = s.regs.rcx ∧
      (tableEntryState s base descriptor kind).regs.rax.toBitVec = descriptor := by
  refine ⟨(Emit.prepared_atBody s descriptor _).routed base kind, rfl, ?_⟩
  exact UInt64.toBitVec_ofBitVec descriptor

end SszX86.CodecEmit
