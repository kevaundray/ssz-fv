import SszX86.CodecErrorMemory

namespace SszX86.CodecMeasureChild.Publish
open SszNative UintCodec BoolCodec
open SszX86.Serialize.Publish

/-- The two copied fields live at child locals+72 and+80, outside its Result. -/
def spillMem (m : DataMem) (sp : BitVec 64) (image : Image) : DataMem :=
  SszX86.Serialize.Publish.spillMem m (sp + 64) image

theorem spill_image (m : DataMem) (sp : BitVec 64) (image : Image)
    (bound : sp.toNat + 168 ≤ 2 ^ 64) (stored : ImageAt m sp image) :
    ImageAt (spillMem m sp image) sp image := by
  rcases stored with ⟨h0,h1,h2,h3,h4,h5,h6,h7,ht,hp⟩
  simp only [BitVec.add_zero] at h0
  constructor <;>
    simp (disch := first | assumption | omega | decide) only
      [spillMem, SszX86.Serialize.Publish.spillMem, BitVec.add_assoc, BitVec.reduceAdd,
        local_read (extent := 168), BitVec.add_zero]
  all_goals assumption

theorem spill_reads (m : DataMem) (sp : BitVec 64) (image : Image)
    (bound : sp.toNat + 168 ≤ 2 ^ 64) :
    Mem.loadInt (spillMem m sp image) (sp + 72) 8 = some (image.w0.toNat : Int) ∧
    Mem.loadInt (spillMem m sp image) (sp + 80) 8 = some (image.w1.toNat : Int) := by
  constructor <;>
    simp (disch := first | assumption | omega | decide) only
      [spillMem, SszX86.Serialize.Publish.spillMem, BitVec.add_assoc, BitVec.reduceAdd,
        local_read (extent := 168), load_store_word]

theorem spill_frame (m : DataMem) (sp : BitVec 64) (image : Image) :
    Emit.MemoryFrame m (spillMem m sp image) (fun a => Emit.InSpan a (sp + 72) 16) := by
  simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
    SszX86.Serialize.Publish.spill_frame m (sp + 64) image

theorem spill_mapping (m : DataMem) (sp : BitVec 64) (image : Image) :
    BitVector.Mapping.Extends m (spillMem m sp image) :=
  SszX86.Serialize.Publish.spill_mapping m (sp + 64) image

def loaded (s : MachineData) (image : Image) : MachineData :=
  {s with regs := {s.regs with
    rax := UInt64.ofBitVec (image.tag.setWidth 64),
    rcx := UInt64.ofBitVec image.w0, rdx := UInt64.ofBitVec image.w1,
    r12 := UInt64.ofBitVec image.w2, r8 := UInt64.ofBitVec image.w3,
    rdi := UInt64.ofBitVec image.w4},
    dmem := spillMem s.dmem s.regs.rsp.toBitVec image}

def tested (s : MachineData) (image : Image) (flags : StatusFlags) : MachineData :=
  {loaded s image with status := flags}

def copied (s : MachineData) (image : Image) (flags : StatusFlags) : MachineData :=
  {tested s image flags with regs := {(loaded s image).regs with
    rcx := UInt64.ofBitVec (image.padding.setWidth 64),
    rdx := UInt64.ofBitVec image.w0, rsi := UInt64.ofBitVec image.w1},
    dmem := copyMem (spillMem s.dmem s.regs.rsp.toBitVec image) s.regs.rbx.toBitVec image}

end SszX86.CodecMeasureChild.Publish
