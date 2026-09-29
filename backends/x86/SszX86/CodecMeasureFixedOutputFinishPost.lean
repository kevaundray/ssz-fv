import SszX86.CodecMeasureFixedOutputFinishMemory

namespace SszX86.CodecMeasureFixed.Output
open SszNative UintCodec

/-- A completed publication's physical observations and frame close the original
public contract after the actual restoring epilogue. This is a memory/ABI lemma,
not an assumed execution of the prefix or of publication. -/
theorem publication_post {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (published : MachineData)
    (sp : published.regs.rsp.toBitVec = body.regs.rsp.toBitVec)
    (simd : published.zmms = body.zmms)
    (publication : Codec.MemoryFrame body.dmem published.dmem
      (ResultWrites original.regs.rdi.toBitVec
        (FixedSize.measureFixed desc (arenaState address capacity used)).result))
    (observed : ResultAt (widthLoad published.dmem) original.regs.rdi.toNat
      (FixedSize.measureFixed desc (arenaState address capacity used)).result) :
    Post original desc address capacity used ra bytes
      (returned published (originalSaved original ra), Int64.ofBitVec ra) := by
  have frame := pending.published_frame published.dmem publication
  have saved : SavedAt published.dmem published.regs.rsp.toBitVec (originalSaved original ra) := by
    rw [sp]
    apply SavedAt.frame body.dmem published.dmem body.regs.rsp.toBitVec
      (originalSaved original ra) _ publication
    · intro i hi written
      exact saved_output_safe owned pending i hi (result_writes_span _ _ _ written)
    · exact pending.saved
  have headerLoad (off : Nat) (inside : off+8 ≤ 16) :
      Mem.loadInt published.dmem (original.regs.rdx.toBitVec + BitVec.ofNat 64 off) 8 =
        Mem.loadInt original.dmem (original.regs.rdx.toBitVec + BitVec.ofNat 64 off) 8 := by
    apply memmove_loadInt_congr
    intro i hi
    apply frame
    intro write
    have mutable := writable_mutable original desc address capacity used bytes
      owned.arena_bound owned.used_bound _ write
    have safe := owned.header_safe (off+i) (by omega)
    rw [BitVec.ofNat_add, ← BitVec.add_assoc] at safe
    exact safe mutable
  refine ⟨returned_abi original published ra (sp.trans pending.sp)
    (simd.trans pending.simd) saved, observed, ?_, ?_, frame, ?_, ?_⟩
  · exact (publication_cursor owned body.dmem published.dmem _ publication).trans pending.cursor
  · exact publication_calls owned body.dmem published.dmem publication pending.calls
  · intro readFootprint stored safe
    exact stored.frame frame safe
  · have addressLoad := (headerLoad 0 (by decide)).trans (by simpa using owned.address_load)
    have capacityLoad := (headerLoad 8 (by decide)).trans owned.capacity_load
    constructor
    · unfold widthLoad
      simpa only [BitVec.ofNat_toNat, BitVec.add_zero, addressLoad, Option.map_some,
        Int.toNat_natCast] using congrArg (Option.map Int.toNat) addressLoad
    · unfold widthLoad
      rw [width_address]
      simpa only [capacityLoad, Option.map_some, Int.toNat_natCast]
        using congrArg (Option.map Int.toNat) capacityLoad

/-- The finite PC694 epilogue closes Post from a completed concrete publication. -/
theorem finish_published {original body : MachineData} {base : Int64} {r : Codec.Footprint}
    {desc : SszNative.Codec.Desc} {address capacity used ra : BitVec 64} {bytes : Nat}
    (e : Executable) (code : CodeAt e base)
    (owned : Owned original base r desc address capacity used ra bytes)
    (pending : Pending original desc address capacity used ra bytes body)
    (published : MachineData)
    (sp : published.regs.rsp.toBitVec = body.regs.rsp.toBitVec)
    (simd : published.zmms = body.zmms)
    (publication : Codec.MemoryFrame body.dmem published.dmem
      (ResultWrites original.regs.rdi.toBitVec
        (FixedSize.measureFixed desc (arenaState address capacity used)).result))
    (observed : ResultAt (widthLoad published.dmem) original.regs.rdi.toNat
      (FixedSize.measureFixed desc (arenaState address capacity used)).result) :
    Eventually (step e) (Post original desc address capacity used ra bytes) (published, base + 694) := by
  apply epilogue e base code published (originalSaved original ra)
  · rw [sp]
    apply SavedAt.frame body.dmem published.dmem body.regs.rsp.toBitVec
      (originalSaved original ra) _ publication
    · intro i hi written
      exact saved_output_safe owned pending i hi (result_writes_span _ _ _ written)
    · exact pending.saved
  · exact publication_post owned pending published sp simd publication observed

end SszX86.CodecMeasureFixed.Output
