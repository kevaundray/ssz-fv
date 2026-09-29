import SszX86.CodecMeasureChildDecode
import SszX86.CodecMeasureChildPublishMemory

namespace SszX86.CodecMeasureChild.Publish
open SszNative UintCodec BoolCodec
open SszX86.Serialize.Publish

macro "codec_child_publish_store " row:num " at " off:num " width " count:num
    &"capacity" total:num " using " code:term:max &"mapped" hm:term:max : tactic => do
  let obtainLoad ← if off.getNat == 0 then
    `(tactic| apply Delimited.mapped_load_zero (capacity := $total) (byteCount := $count))
  else
    `(tactic| apply Large.mapped_load (capacity := $total) («offset» := $off) («width» := $count))
  `(tactic|
    (codec_measure_child_step $row using $code
     try simp only [BitVec.ofInt_add, BitVec.ofInt_toInt]
     apply Delimited.store_cps
     · $obtainLoad
       · have mappingBase := $hm
         repeat' first | apply Large.mapped_store | assumption
       · decide
     simp only [Effects.All]))

macro "codec_child_publish_read " row:num " using " code:term " word " hl:term : tactic => `(tactic|
  (codec_measure_child_step $row using $code
   simp (disch := first | assumption | omega | decide)
     [MachineData.load, Width.bytes, Width.bits, Effects.All,
      BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.add_assoc,
      local_read (extent := 168), remote_read (srcCount := 168) (dstCount := 72),
      ($hl), Delimited.word_cast]))

/-- Every source byte comes from the actual returned temporary; inactive padding
is loaded only through its original mapped Image, never from a semantic error. -/
theorem loads_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (image : Image)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 168)
    (bound : s.regs.rsp.toNat + 168 ≤ 2 ^ 64)
    (stored : ImageAt s.dmem s.regs.rsp.toBitVec image) (P : MachineState → Prop)
    (next : Eventually (step e) P (loaded s image, base + 144)) :
    Eventually (step e) P (s, base + 106) := by
  have preserved := spill_image s.dmem s.regs.rsp.toBitVec image bound stored
  have post2 := preserved.w2
  have post3 := preserved.w3
  have post4 := preserved.w4
  simp only [spillMem, SszX86.Serialize.Publish.spillMem,
    BitVec.add_assoc, BitVec.reduceAdd] at post2 post3 post4
  rcases stored with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_zero] at h0
  codec_child_publish_read 31 using code word ht
  codec_child_publish_read 32 using code word h0
  codec_child_publish_read 33 using code word h1
  codec_child_publish_store 34 at 72 width 8 capacity 168 using code mapped stack
  codec_child_publish_store 35 at 80 width 8 capacity 168 using code mapped stack
  codec_child_publish_read 36 using code word post2
  codec_child_publish_read 37 using code word post3
  codec_child_publish_read 38 using code word post4
  simpa [loaded, spillMem, SszX86.Serialize.Publish.spillMem,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.add_assoc] using next

theorem branch_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (image : Image) (P : MachineState → Prop)
    (success : image.tag = 0 → ∀ flags,
      Eventually (step e) P (tested s image flags, base + 219))
    (failure : image.tag ≠ 0 → ∀ flags,
      Eventually (step e) P (tested s image flags, base + 148)) :
    Eventually (step e) P (loaded s image, base + 144) := by
  have target := code.targets ("codec_measure_child_u219", 219) (by decide)
  unfold loaded
  codec_measure_child_step 39 using code
  constructor <;> codec_measure_child_step 40 using code
  all_goals
    simp [StatusFlags.from_result]
    by_cases zero : image.tag = 0#32
    · simpa [tested, loaded, target, zero, Effects.All] using success zero _
    · simpa [tested, loaded, target, zero, Effects.All] using failure zero _

theorem copy_cps (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (image : Image) (flags : StatusFlags)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (bound : s.regs.rsp.toNat + 168 ≤ 2 ^ 64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 168 72)
    (stored : ImageAt s.dmem s.regs.rsp.toBitVec image) (P : MachineState → Prop)
    (next : Eventually (step e) P (copied s image flags, base + 622)) :
    Eventually (step e) P (tested s image flags, base + 148) := by
  have preserved := spill_image s.dmem s.regs.rsp.toBitVec image bound stored
  rcases preserved with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_zero] at h0
  have spills := spill_reads s.dmem s.regs.rsp.toBitVec image bound
  have hmap := spill_mapping s.dmem s.regs.rsp.toBitVec image _ _ result
  unfold tested loaded
  codec_child_publish_read 41 using code word h7
  codec_child_publish_store 42 at 56 width 8 capacity 72 using code mapped hmap
  codec_child_publish_read 43 using code word h5
  codec_child_publish_read 44 using code word h6
  codec_child_publish_store 45 at 48 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 46 at 40 width 8 capacity 72 using code mapped hmap
  codec_child_publish_read 47 using code word hp
  codec_child_publish_read 48 using code word spills.1
  codec_child_publish_read 49 using code word spills.2
  codec_child_publish_store 50 at 8 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 51 at 0 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 52 at 16 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 53 at 24 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 54 at 32 width 8 capacity 72 using code mapped hmap
  codec_child_publish_store 55 at 64 width 4 capacity 72 using code mapped hmap
  codec_child_publish_store 56 at 68 width 4 capacity 72 using code mapped hmap
  codec_measure_child_step 57 using code
  simpa [copied, tested, loaded, copyMem, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_setWidth_of_le] using next

theorem failure_runs (e : Executable) (base : Int64) (code : CodeAt e base)
    (s : MachineData) (image : Image) (reason : SszNative.Codec.Error)
    (stack : Large.Mapped s.dmem s.regs.rsp.toBitVec 168)
    (result : Large.Mapped s.dmem s.regs.rbx.toBitVec 72)
    (bound : s.regs.rsp.toNat + 168 ≤ 2 ^ 64)
    (apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rbx.toBitVec 168 72)
    (stored : ImageAt s.dmem s.regs.rsp.toBitVec image)
    (error : Codec.ErrorAt (widthLoad s.dmem) s.regs.rsp.toNat reason) :
    Eventually (step e) (fun t => ∃ flags, t = (copied s image flags, base + 622))
      (s, base + 106) := by
  apply loads_cps e base code s image stack bound stored
  apply branch_cps e base code s image
  · intro zero
    exact False.elim (Codec.ErrorAt.image_nonzero stored error zero)
  · intro nonzero flags
    apply copy_cps e base code s image flags result bound apart stored
    exact Eventually.done _ ⟨flags, rfl⟩

end SszX86.CodecMeasureChild.Publish
