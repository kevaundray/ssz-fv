import SszX86.MeasureEntryOwned
import SszX86.MeasureReturnMemory

namespace SszX86.Measure
open SszNative SszNative.Serialize UintCodec

theorem bodyWritable_original {s b : MachineData} (anchors : AtBody s b)
    (outcome : Outcome NatOperand) (a : BitVec 64)
    (written : BodyWritable b outcome a) : Writable s outcome a := by
  rcases written with result | allocation | cursor | ⟨i, hi, equal⟩
  · exact Or.inl (by simpa only [anchors.result] using result)
  · exact Or.inr (Or.inl allocation)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [anchors.arenaPointer] using cursor)))
  · refine Or.inr (Or.inr (Or.inr ⟨i, by omega, ?_⟩))
    rw [anchors.stack] at equal
    simpa only [BitVec.sub_sub, show (264 : BitVec 64) + 16 = 280 by decide] using equal

theorem BodyPost.original_frame {s b t : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used : BitVec 64}
    (post : BodyPost b desc value buffer address capacity used t)
    (anchors : AtBody s b) :
    MemoryFrame s.dmem t.dmem (Writable s (measure desc value (arenaState address capacity used))) := by
  intro a outside
  calc
    t.dmem.get? a = b.dmem.get? a := post.frame a
      (fun written => outside (bodyWritable_original anchors _ a written))
    _ = (savedMem s).get? a := by rw [anchors.memory]
    _ = s.dmem.get? a := saved_frame s a
      (fun inside => outside (Or.inr (Or.inr (Or.inr inside))))

/-- The actual RET result has the exact original input/result addresses and ABI.
The body frame and real prologue frame compose bytewise, including padding. -/
theorem BodyPost.returned_post {s b t : MachineData} {desc : Desc} {value : Value}
    {buffer address capacity used ra : BitVec 64}
    (post : BodyPost b desc value buffer address capacity used t)
    (anchors : AtBody s b) :
    Post s desc value buffer address capacity used ra
      (returned t (SszX86.Measure.saved s ra), Int64.ofBitVec ra) := by
  have stack : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec - 264 := by
    rw [post.stack]
    exact anchors.stack
  refine {
    abi := ?_
    observed := ?_
    cursor := ?_
    header := ?_
    calls := post.calls
    descriptor := ?_
    valueStored := ?_
    frame := post.original_frame anchors }
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, post.vectors.trans anchors.vectors⟩
    · simp only [returned, UInt64.toBitVec_ofBitVec, stack]
      bv_omega
    all_goals rfl
  · simpa only [returned, anchors.result] using post.observed
  · simpa only [returned, anchors.arenaPointer] using post.cursor
  · simpa only [returned, anchors.arenaPointer] using post.header
  · simpa only [returned, anchors.descriptorPointer] using post.descriptor
  · simpa only [returned, anchors.valuePointer] using post.valueStored

/-- All saved words and the original return address are recovered from original
ownership and the proved exact body footprint, then the genuine epilogue runs. -/
theorem finish_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s b t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64) (retain : Bool)
    (owned : Owned s base desc value buffer address capacity used ra retain)
    (anchors : AtBody s b)
    (tag : b.regs.rax.toBitVec.setWidth 8 = BitVec.ofNat 8 (valueTag value))
    (post : BodyPost b desc value buffer address capacity used t) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (t, base + 3335) := by
  have bodyOwned := owned.at_body anchors tag
  have initialSaved : SavedAt b.dmem b.regs.rsp.toBitVec (saved s ra) := by
    rw [anchors.memory, anchors.stack]
    exact saved_at s ra owned.returnSlot
  apply epilogue e base hc t (saved s ra) (post.saved bodyOwned _ initialSaved)
  exact post.returned_post anchors

end SszX86.Measure
