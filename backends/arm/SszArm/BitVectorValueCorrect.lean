import SszArm.BitVectorValueTail

namespace SszArm.BitVector.ValueTail

open Delimited (MemoryFrame Protected)
open UintCodec (widthLoad)

/-- The terminal continuation's result at the existing epilogue entry. The
precise frame preserves saved activation words and any readonly aliases that
are physically separated from the four actual writable spans. -/
structure Post (s t : ArmState) (base : BitVec 64) (count : BitVec 128)
    (data : Ssz.Bytes) : Prop where
  pc : read_pc t = base + 4732#64
  error : read_err t = .None
  sp : r (.GPR 31#5) t = r (.GPR 31#5) s
  resultAt : SszNative.BitVector.ResultAt (widthLoad t)
    (r (.GPR 23#5) s).toNat (r (.GPR 24#5) s).toNat data (.ok count)
  frame : MemoryFrame (writes s) s t
  registers : ∀ reg : BitVec 5, 19 ≤ reg.toNat → reg.toNat ≤ 30 →
    r (.GPR reg) t = r (.GPR reg) s
  vectors : ∀ reg : BitVec 5, r (.SFP reg) t = r (.SFP reg) s
  program : t.program = s.program

/-- No native guard outcome and no canonical or u64-sized count premise occurs
in this contract. Scope is the full-Nat helper predicate, and Some is derived
from that predicate before interpreting the actual private helper bytes. -/
theorem correct_of_scope (s : ArmState) (base : BitVec 64)
    (length expected : SszNative.NatOperand) (remainder : BitVec 64) (data : Ssz.Bytes)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 6592#64)
    (arithmetic : SszNative.BitVector.Expected length expected remainder)
    (scope : SszNative.NatNarrow.runExact expected (r (.GPR 20#5) s) = true)
    (observed : SszNative.NatNarrow.U128ResultAt (widthLoad s)
      ((r (.GPR 31#5) s).toNat + 144) (SszNative.NatNarrow.toU128 length))
    (size : (r (.GPR 20#5) s).toNat = data.size)
    (dataAt : SszNative.ByteView.BytesAt (widthLoad s) (r (.GPR 24#5) s).toNat data)
    (dataBound : (r (.GPR 24#5) s).toNat + data.size ≤ 2^64)
    (dataOwned : Protected (writes s) (r (.GPR 24#5) s).toNat data.size) :
    Post s (run (fuel s base) s) base (BitVec.ofNat 128 length.value) data := by
  rw [executes_of_scope s base length expected remainder space code error aligned pc
    arithmetic scope observed]
  have narrowed := SszNative.BitVector.scope_narrows length expected remainder (r (.GPR 20#5) s)
    arithmetic scope
  refine ⟨final_pc s base, (final_error s base).trans error, final_sp s base,
    ?_, final_frame s base space, final_register s base, final_vector s base,
    final_program s base⟩
  apply final_result s base space (BitVec.ofNat 128 length.value) data
    (by simpa only [narrowed.2.1] using observed) size narrowed.2.2 dataAt dataBound dataOwned

theorem Post.readonly {s t : ArmState} {base : BitVec 64} {count : BitVec 128}
    {data : Ssz.Bytes} (post : Post s t base count data) (address bytes : Nat)
    (physical : address + bytes ≤ 2^64) (owned : Protected (writes s) address bytes) :
    widthLoad t address bytes = widthLoad s address bytes :=
  post.frame.load address bytes physical owned

end SszArm.BitVector.ValueTail
