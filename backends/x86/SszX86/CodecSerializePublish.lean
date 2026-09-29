import SszX86.CodecSerializeCode
import SszX86.CodecErrorMemory

namespace SszX86.CodecSerialize.Publish
open SszNative UintCodec BoolCodec
open SszX86.Serialize.Publish

/-- The wrapper's native return area is 72 bytes. Reads after earlier stores
therefore need only separation from those 72 bytes, not an invented 80-byte
result object. -/
macro "codec_publish_read " row:num " using " hc:term " publishWord " hl:term : tactic => `(tactic|
  (publish_step $row using $hc
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      local_read (extent := 96), remote_read (srcCount := 96) (dstCount := 72),
      ($hl), Delimited.word_cast]))

theorem copy_cps (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s : MachineData) (image : Image) (flags : StatusFlags)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 72)
    (stored : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (copied s image flags, base + 410)) :
    Eventually (step e) P (tested s image flags, base + 90) := by
  have hc := code.wrapper
  have preserved := spill_plan s.dmem s.regs.rsp.toBitVec image bound stored
  rcases preserved with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 ht hp
  have spills := spill_reads s.dmem s.regs.rsp.toBitVec image bound
  have hmap := spill_mapping s.dmem s.regs.rsp.toBitVec image _ _ result
  unfold tested loaded
  codec_publish_read 25 using hc publishWord h7
  publish_store 26 at 56 width 8 capacity 72 using hc mapped hmap
  codec_publish_read 27 using hc publishWord h5
  codec_publish_read 28 using hc publishWord h6
  publish_store 29 at 48 width 8 capacity 72 using hc mapped hmap
  publish_store 30 at 40 width 8 capacity 72 using hc mapped hmap
  codec_publish_read 31 using hc publishWord hp
  codec_publish_read 32 using hc publishWord spills.1
  codec_publish_read 33 using hc publishWord spills.2
  publish_store 34 at 8 width 8 capacity 72 using hc mapped hmap
  publish_store 35 at 0 width 8 capacity 72 using hc mapped hmap
  publish_store 36 at 16 width 8 capacity 72 using hc mapped hmap
  publish_store 37 at 24 width 8 capacity 72 using hc mapped hmap
  publish_store 38 at 32 width 8 capacity 72 using hc mapped hmap
  publish_store 39 at 64 width 4 capacity 72 using hc mapped hmap
  publish_store 40 at 68 width 4 capacity 72 using hc mapped hmap
  publish_step 41 using hc
  simpa [copied, tested, loaded, copyMem, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_setWidth_of_le] using next

theorem failure_cps (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s : MachineData) (image : Image)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 72)
    (stored : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (nonzero : image.tag ≠ 0) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (copied s image flags, base + 410)) :
    Eventually (step e) P (s, base + 47) := by
  apply loads_cps e base code.wrapper s image stack bound stored P
  apply branch_cps e base code.wrapper s image P
  · intro zero
    exact False.elim (nonzero zero)
  · intro _ flags
    exact copy_cps e base code s image flags result bound apart stored P (next flags)

theorem capacity_cps (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s : MachineData) (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (capacityFailed s, base + 410)) :
    Eventually (step e) P (s, base + 313) := by
  have hc := code.wrapper
  publish_store 75 at 0 width 8 capacity 72 using hc mapped hmap
  publish_store 76 at 8 width 8 capacity 72 using hc mapped hmap
  publish_store 77 at 16 width 8 capacity 72 using hc mapped hmap
  publish_store 78 at 24 width 8 capacity 72 using hc mapped hmap
  publish_store 79 at 32 width 8 capacity 72 using hc mapped hmap
  publish_store 80 at 40 width 8 capacity 72 using hc mapped hmap
  publish_store 81 at 48 width 8 capacity 72 using hc mapped hmap
  publish_store 82 at 56 width 8 capacity 72 using hc mapped hmap
  publish_store 83 at 64 width 4 capacity 72 using hc mapped hmap
  publish_step 84 using hc
  simpa [capacityFailed, capacityMem] using next

theorem host_cps (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s : MachineData) (hmap : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (hostFailed s, base + 410)) :
    Eventually (step e) P (s, base + 235) := by
  have hc := code.wrapper
  publish_store 61 at 56 width 8 capacity 72 using hc mapped hmap
  publish_store 62 at 48 width 8 capacity 72 using hc mapped hmap
  publish_store 63 at 40 width 8 capacity 72 using hc mapped hmap
  publish_store 64 at 32 width 8 capacity 72 using hc mapped hmap
  publish_store 65 at 24 width 8 capacity 72 using hc mapped hmap
  publish_store 66 at 16 width 8 capacity 72 using hc mapped hmap
  publish_store 67 at 8 width 8 capacity 72 using hc mapped hmap
  publish_store 68 at 0 width 8 capacity 72 using hc mapped hmap
  publish_step 69 using hc
  publish_store 83 at 64 width 4 capacity 72 using hc mapped hmap
  publish_step 84 using hc
  simpa [hostFailed, hostMem] using next

/-- Original measured failure to the real epilogue; padding is copied as the
arbitrary mapped word actually present, not materialized from a semantic Plan. -/
theorem failure_runs (e : Executable) (base : Int64) (code : CodecSerialize.CodeAt e base)
    (s : MachineData) (image : Image) (reason : SszNative.Codec.Error)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 96)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (bound : s.regs.rsp.toNat + 96 ≤ 2^64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 96 72)
    (stored : ImageAt s.dmem (s.regs.rsp.toBitVec + 24#64) image)
    (error : Codec.ErrorAt (widthLoad s.dmem)
      (s.regs.rsp.toBitVec + 24#64).toNat reason) :
    Eventually (step e)
      (fun t => ∃ flags, t = (copied s image flags, base + 410)) (s, base + 47) := by
  apply failure_cps e base code s image stack result bound apart stored
    (Codec.ErrorAt.image_nonzero stored error)
  intro flags
  exact Eventually.done _ ⟨flags, rfl⟩

end SszX86.CodecSerialize.Publish
