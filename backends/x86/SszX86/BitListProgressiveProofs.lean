import SszX86.BitListProgressiveOwned

namespace SszX86.BitList
open SszNative UintCodec BoolCodec

theorem progressive_post (s : MachineData) (saved : Saved) (limit : Option Nat)
    (data : Ssz.Bytes) (address capacity used : BitVec 64)
    (h : ProgressiveOwned s saved limit data address capacity used) (t : MachineState)
    (post : Delimited.Post (progressiveState s saved) limit data address capacity used saved.rip t) :
    Post s saved true limit data address capacity used t := by
  have sp := progressive_spNat s saved h.stack_bound
  have opt := progressive_optionNat s saved h.descriptor.bound
  refine ⟨?_, post.prepared, ?_, ?_, post.cursor⟩
  · have observed := post.observed
    rw [opt] at observed
    exact observed
  · refine ⟨post.returned.pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, post.returned.simd, ?_⟩
    · have hs := post.returned.sp
      simp only [progressiveState, UInt64.toBitVec_ofBitVec] at hs
      rw [hs]
      bv_omega
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.rbx
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.rbp
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.r12
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.r13
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.r14
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using congrArg UInt64.toBitVec post.returned.r15
    · simpa only [progressiveState, UInt64.toBitVec_ofBitVec] using post.returned.returnSlot
  · intro a out work arena
    apply post.frame a out
    · rw [sp]
      have active := activation_le data
      simp only [workStart, workBytes, ↓reduceIte] at work
      unfold Body.Outside at *
      omega
    · exact arena

/-- Actual ProgressiveBitList entry1240 through the original caller RET. The
restored wrapper activation is available to the tail callee, including paths
which commit a count buffer and subsequently reject its bound. -/
theorem progressive_correct (e : Executable) (base : Int64) (code : JointCodeAt e base)
    (s : MachineData) (saved : Saved) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used : BitVec 64)
    (h : ProgressiveOwned s saved limit data address capacity used) :
    Eventually (step e) (Post s saved true limit data address capacity used)
      (s, base + Int64.ofNat progressiveEntry) := by
  apply progressive_entry_cps e base code.body s saved h.saved
  have runs := Delimited.decode_correct e (base + Int64.ofInt delimitedOffset)
    code.delimited code.compare (progressiveState s saved) limit data address capacity used
    saved.rip (progressive_owned s saved limit data address capacity used h)
  rw [show Int64.ofNat Delimited.entry = 0 by decide, Int64.add_zero] at runs
  exact eventually_weaken (step e)
    (Delimited.Post (progressiveState s saved) limit data address capacity used saved.rip)
    (Post s saved true limit data address capacity used)
    (progressiveState s saved, base + Int64.ofInt delimitedOffset)
    (fun t post => progressive_post s saved limit data address capacity used h t post) runs

/-- Exact shared resource exhaustion remains distinct from all pinned SSZ
semantic outcomes. No arena-success or bound-success premise is present. -/
theorem Post.outcome {s : MachineData} {saved : Saved} {tail : Bool} {limit : Option Nat}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (owned : Owned s saved tail data address capacity used)
    (post : Post s saved tail limit data address capacity used t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (SszNative.BitView.delimitedOutcome limit data) := by
  have physical : data.size < 2^64 := by rw [owned.length]; exact s.regs.r14.toBitVec.isLt
  by_cases exhausted : SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩
  · rw [ite_eq_left exhausted]
    have result := (SszNative.Delimited.run_scratch_iff limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical).mpr exhausted
    simpa only [SszNative.Delimited.ResultAt, result] using post.observed
  · rw [ite_eq_right exhausted]
    exact SszNative.Delimited.result_refines _ _ _ _ limit data
      ⟨address.toNat, capacity.toNat, used.toNat⟩ physical exhausted post.observed

theorem Post.progressive_refines {s : MachineData} {saved : Saved} {limit : Option Nat}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (owned : Owned s saved true data address capacity used)
    (post : Post s saved true limit data address capacity used t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (Ssz.deserialize (.progressiveBitList limit) data) := by
  simpa only [SszNative.BitView.progressive_outcome_eq_deserialize] using post.outcome owned

theorem Post.list_refines {s : MachineData} {saved : Saved} {cap : Nat}
    {data : Ssz.Bytes} {address capacity used : BitVec 64} {t : MachineState}
    (owned : Owned s saved false data address capacity used)
    (post : Post s saved false (some cap) data address capacity used t) :
    if SszNative.Delimited.Exhausted data ⟨address.toNat, capacity.toNat, used.toNat⟩ then
      SszNative.UintCodec.errorAt (widthLoad t.1.dmem) s.regs.rdi.toNat 32768 0 0
    else SszNative.BitView.ResultAt (widthLoad t.1.dmem) s.regs.rdi.toNat
      (Ssz.deserialize (.bitList cap) data) := by
  simpa only [SszNative.BitView.list_outcome_eq_deserialize] using post.outcome owned

end SszX86.BitList
