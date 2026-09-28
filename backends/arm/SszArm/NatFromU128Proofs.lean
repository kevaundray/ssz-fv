import SszArm.NatFromU128Contract

namespace SszArm.NatFromU128

open UintCodec (widthLoad)
open Delimited (Span Protected MemoryFrame Returned)

private theorem prefix_returned {s u : ArmState} (reached : Checkpoint s u)
    (body : Body) (he : read_err s = .None) : Returned s (body.final u) := by
  have returned := body_returned body u (reached.frame.error.trans he)
  refine ⟨returned.pc.trans (reached.frame.registers 30#5 (by decide)),
    returned.error, returned.sp.trans reached.frame.sp, ?_, ?_⟩
  · intro reg low high
    apply (returned.registers reg low high).trans
    apply reached.frame.registers
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    bv_omega
  · intro reg low high
    rw [returned.vectors reg low high, reached.frame.vectors]

private theorem prefix_frame {s u t : ArmState} (reached : Checkpoint s u)
    (writes : List Span) (frame : MemoryFrame writes u t) : MemoryFrame writes s t := by
  intro a outside
  rw [frame a outside, reached.memory]

private theorem success_frame_local {s t : ArmState} (frame : MemoryFrame (successWrites s) s t) :
    MemoryFrame (localWrites s) s t := by
  intro a outside
  have out := outside ((r (.GPR 0#5) s).toNat, 68) (by simp [localWrites])
  have work := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [localWrites])
  apply frame a
  intro span member
  simp only [successWrites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> omega

private theorem local_header {s t : ArmState} (owned : Owned s)
    (frame : MemoryFrame (localWrites s) s t) (offset : Nat) (within : offset + 8 ≤ 24) :
    read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) t =
      read_mem_bytes 8 (r (.GPR 4#5) s + BitVec.ofNat 64 offset) s := by
  have bound := owned.header
  have address : (r (.GPR 4#5) s + BitVec.ofNat 64 offset).toNat =
      (r (.GPR 4#5) s).toNat + offset := by bv_omega
  apply frame.read
  · rw [address]; omega
  · rw [address]
    exact owned.headerLocal.subspan offset 8 within

private theorem wide_header (s : ArmState) (space : WideSpace s) :
    read_mem_bytes 8 (r (.GPR 4#5) s) (Body.wide.final s) = addressWord s ∧
    read_mem_bytes 8 (r (.GPR 4#5) s + 8#64) (Body.wide.final s) = capacityWord s := by
  have frame := wide_frame s space
  have headerProtected : Protected (wideWrites s) (r (.GPR 4#5) s).toNat 16 := by
    right
    intro span member
    simp only [wideWrites, successWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | (rfl | rfl)
    all_goals
      have ho := space.headerOutput
      have hs := space.headerStack
      have hp := space.payloadHeader
      have stack := space.stack
      omega
  have bound := space.header
  constructor
  · apply frame.read
    · omega
    · simpa only [Nat.add_zero] using headerProtected.subspan 0 8 (by decide)
  · apply frame.read
    · bv_omega
    · have addr : (r (.GPR 4#5) s + 8#64).toNat = (r (.GPR 4#5) s).toNat + 8 := by bv_omega
      rw [addr]
      exact headerProtected.subspan 8 8 (by decide)

/-- Complete actual standalone helper: original entry, every error check, real
LR return, original SP/ABI, exact private Result, cursor, and physical writes. -/
theorem correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (owned : Owned s) :
    ∃ fuel t, run fuel s = t ∧ Post s t := by
  obtain ⟨fuel, u, body, runs, reached, selected⟩ := entry_runs s base hc he ha hp owned.toSpace
  refine ⟨fuel, body.final u, runs, ?_⟩
  have out := reached.frame.registers 0#5 (by decide)
  have low := reached.frame.registers 2#5 (by decide)
  have high := reached.frame.registers 3#5 (by decide)
  have hdr := reached.frame.registers 4#5 (by decide)
  have space := reached.frame.space owned.toSpace
  have returned := prefix_returned reached body he
  cases body
  · have model := outcome_small s selected
    have frame : MemoryFrame (successWrites s) s (Body.small.final u) := by
      apply prefix_frame reached
      simpa only [successWrites, out, reached.frame.sp] using small_frame u space
    have localFrame := success_frame_local frame
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [SszNative.NatArithmetic.unchanged, out, low] using small_result u space
    · rw [model]
      exact congrArg BitVec.toNat (local_header owned localFrame 16 (by decide))
    · exact ⟨by simpa using local_header owned localFrame 0 (by decide),
        local_header owned localFrame 8 (by decide)⟩
    · simpa only [writesFor, model, SszNative.NatArithmetic.unchanged, List.append_nil] using frame
    · intro reservation allocated
      simp only [model, SszNative.NatArithmetic.unchanged] at allocated
      contradiction
  · have model := outcome_failure s selected.1 selected.2
    have frame : MemoryFrame (localWrites s) s (Body.failure.final u) := by
      apply prefix_frame reached
      simpa only [localWrites, out, reached.frame.sp] using failure_frame u space
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [SszNative.NatArithmetic.unchanged, out] using failure_result u space
    · rw [model]
      exact congrArg BitVec.toNat (local_header owned frame 16 (by decide))
    · exact ⟨by simpa using local_header owned frame 0 (by decide),
        local_header owned frame 8 (by decide)⟩
    · simpa only [writesFor, model, SszNative.NatArithmetic.unchanged, List.append_nil] using frame
    · intro reservation allocated
      simp only [model, SszNative.NatArithmetic.unchanged] at allocated
      contradiction
  · obtain ⟨geometry, pointerNat⟩ := owned.wideSpace reached selected
    rcases selected with ⟨large, checks, address, first, last⟩
    have model := outcome_wide s large checks
    have ptr : pointer u = BitVec.ofNat 64 ((addressWord s).toNat +
        SszNative.Arena.start (addressWord s).toNat (usedWord s).toNat) := by
      rw [← pointerNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have result := wide_result u geometry
    have immutable := wide_header u geometry
    refine ⟨returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [model]
      simpa only [out, low, high, ptr] using result
    · rw [model, ← hdr, wide_cursor u geometry]
      exact last
    · constructor
      · rw [← hdr, immutable.1]
        simpa only [BitVec.add_zero] using reached.header 0#64
      · rw [← hdr, immutable.2]
        exact reached.header 8#64
    · apply prefix_frame reached
      simpa only [writesFor, model, wideWrites, successWrites,
        out, hdr, reached.frame.sp, pointerNat] using wide_frame u geometry
    · intro reservation allocated
      rw [model] at allocated ⊢
      cases allocated
      simpa only [ptr, low, high] using result.1.2.2

/-- The zero-high-word entry needs no arena validity, capacity, header, or
free-suffix hypothesis at all, and writes only Small's live fields and scratch. -/
theorem small_correct (s : ArmState) (base : BitVec 64)
    (hc : CodeAt s base) (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hp : read_pc s = base) (space : Space s) (small : r (.GPR 3#5) s = 0#64) :
    ∃ fuel t, run fuel s = t ∧ Returned s t ∧
      SszNative.NatArithmetic.AddResultAt (widthLoad t) (r (.GPR 0#5) s).toNat
        (.ok (.small (r (.GPR 2#5) s))) ∧ MemoryFrame (successWrites s) s t := by
  obtain ⟨fuel, u, body, runs, reached, selected⟩ := entry_runs s base hc he ha hp space
  have out := reached.frame.registers 0#5 (by decide)
  have low := reached.frame.registers 2#5 (by decide)
  cases body
  · refine ⟨fuel, Body.small.final u, runs, prefix_returned reached .small he, ?_, ?_⟩
    · simpa only [out, low] using small_result u (reached.frame.space space)
    · apply prefix_frame reached
      simpa only [successWrites, out, reached.frame.sp] using
        small_frame u (reached.frame.space space)
  · exact False.elim (selected.1 small)
  · exact False.elim (selected.1 small)

/-- Returned successful values denote the original full unsigned u128. -/
theorem Post.value {s t : ArmState} (_post : Post s t) (result : SszNative.NatOperand)
    (success : (outcome s).result = .ok result) : result.value = (wide s).toNat :=
  SszNative.NatArithmetic.fromWide_value _ _ _ _ result success

theorem Post.pair {s t : ArmState} (post : Post s t) (result : SszNative.NatOperand)
    (success : (outcome s).result = .ok result) :
    SszNative.NatMemory.Pair (widthLoad t) result.pointer result.payload (wide s).toNat := by
  have stored := post.result
  rw [success] at stored
  have pair := SszNative.NatArithmetic.operandAt.pair _ _ result stored.1
  simpa only [post.value result success] using pair

/-- Memory framing applies to any protected readonly bytes, including the
used arena prefix, padding, and caller storage not listed in the exact frame. -/
theorem Post.protected {s t : ArmState} (post : Post s t) (address bytes : Nat)
    (physical : address + bytes ≤ 2^64) (separate : Protected (writesFor s) address bytes) :
    widthLoad t address bytes = widthLoad s address bytes :=
  post.frame.load address bytes physical separate

end SszArm.NatFromU128
