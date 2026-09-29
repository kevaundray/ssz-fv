import SszX86.HashFinalizeProofs
import SszX86.HashCombineProofs

namespace SszX86.Hash

/-- The machine finalizer refines the pinned hash whenever the present state
represents those bytes. This hypothesis concerns only initial semantic data. -/
theorem finalize_hash_correct (e : Executable) (root : Int64) (code : LinkedCode e root)
    (compression : CompressionCorrect e root) (s : MachineData) (state : Model)
    (ra : BitVec 64) (pre : FinalizePre root s state ra) (input : ByteArray)
    (represents : SszNative.HashStream.Represents state input.data.toList) :
    Eventually (step e) (fun t => Returned s ra t ∧
      BytesAt t.1.dmem s.regs.rdi.toBitVec (Ssz.Sha256.hash input).data.toList ∧
      MemoryFrame s.dmem t.1.dmem (FinalizeWritable s) ∧
      StackAt t.1.dmem s.regs.rsp.toBitVec 192) (s, root - 256) := by
  apply eventually_weaken (step e) _ _ _ _
    (finalize_correct e root code compression s state ra pre)
  intro t post
  refine ⟨post.returned, ?_, post.frame, post.stack⟩
  simpa only [SszNative.HashStream.finalize_eq_hash state input represents] using post.digest

/-- Arbitrary raw slices refine the pinned SHA hash of concatenation. -/
theorem combine_hash_correct (e : Executable) (root : Int64) (code : LinkedCode e root)
    (compression : CompressionCorrect e root) (s : MachineData) (left right : ByteArray)
    (ra : BitVec 64) (pre : CombinePre root s left right ra) :
    Eventually (step e) (fun t => Returned s ra t ∧
      BytesAt t.1.dmem s.regs.rdi.toBitVec (Ssz.Sha256.hash (left ++ right)).data.toList ∧
      BytesAt t.1.dmem s.regs.rsi.toBitVec left.data.toList ∧
      BytesAt t.1.dmem s.regs.rcx.toBitVec right.data.toList ∧
      MemoryFrame s.dmem t.1.dmem (CombineWritable s) ∧
      StackAt t.1.dmem s.regs.rsp.toBitVec 368) (s, root) := by
  apply eventually_weaken (step e) _ _ _ _
    (combine_correct e root code compression s left right ra pre)
  intro t post
  refine ⟨post.returned, ?_, post.left, post.right, post.frame, post.stack⟩
  simpa only [SszNative.HashStream.combine_eq_hash] using post.digest

/-- The public SSZ operation is the same raw two-slice wrapper, not fixed-width chunks. -/
theorem combine_ssz_correct (e : Executable) (root : Int64) (code : LinkedCode e root)
    (compression : CompressionCorrect e root) (s : MachineData) (left right : Ssz.Bytes)
    (ra : BitVec 64) (pre : CombinePre root s ⟨left⟩ ⟨right⟩ ra) :
    Eventually (step e) (fun t => Returned s ra t ∧
      BytesAt t.1.dmem s.regs.rdi.toBitVec (Ssz.combine left right).toList ∧
      BytesAt t.1.dmem s.regs.rsi.toBitVec left.toList ∧
      BytesAt t.1.dmem s.regs.rcx.toBitVec right.toList ∧
      MemoryFrame s.dmem t.1.dmem (CombineWritable s) ∧
      StackAt t.1.dmem s.regs.rsp.toBitVec 368) (s, root) := by
  apply eventually_weaken (step e) _ _ _ _
    (combine_correct e root code compression s ⟨left⟩ ⟨right⟩ ra pre)
  intro t post
  refine ⟨post.returned, ?_, post.left, post.right, post.frame, post.stack⟩
  simpa only [SszNative.HashStream.combine_eq] using post.digest

/-- Both returned observations cover precisely thirty-two bytes. -/
theorem digest_extents (state : Model) (left right : ByteArray) :
    (SszNative.HashStream.finalize state).data.toList.length = 32 ∧
    (SszNative.HashStream.combine left right).data.toList.length = 32 := by
  simp only [Array.length_toList, ByteArray.size_data,
    SszNative.HashStream.finalize_size, SszNative.HashStream.combine_size, and_self]

end SszX86.Hash
