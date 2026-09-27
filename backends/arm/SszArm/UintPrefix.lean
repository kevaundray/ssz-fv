import SszArm.UintWidth
import SszArm.UintSmall

namespace SszArm.UintCodec

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem WidthFrame.small_stable {s t : ArmState} (h : WidthFrame s t) : Small.Stable s t := by
  refine ⟨h.program, h.error, ?_, h.vectors, h.memory⟩
  intro reg hr
  apply h.registers reg
  simp only [Small.Live] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1⟩

def PrefixExit (s t : ArmState) (base : BitVec 64) (width : Nat) (data : Ssz.Bytes) : Prop :=
  if width = data.size then Small.Exit base data t
  else read_pc t = base + 4544#64 ∧
    r (.GPR 8#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 8#64) s ∧
    r (.GPR 9#5) t = read_mem_bytes 8 (r (.GPR 1#5) s + 16#64) s

/-- Actual execution from the UInt body entry to scope-error stores, complete
Small-value stores, or Large allocation preparation. All three paths retain
the same caller-owned input and the same sixteen-byte scratch frame. -/
theorem prefix_runs (s : ArmState) (base : BitVec 64) (width : Nat) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 148#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hheader : (r (.GPR 1#5) s).toNat + 24 ≤ 2^64)
    (hs : WidthScratchSeparated s)
    (hwidth : SszNative.NatMemory.At (widthLoad s) ((r (.GPR 1#5) s).toNat + 8) width)
    (hi : Small.Input s data) :
    ∃ fuel t, run fuel s = t ∧ Small.Stable s t ∧ CodeAt t base ∧
      read_err t = .None ∧ CheckSPAlignment t ∧ Small.Input t data ∧
      PrefixExit s t base width data := by
  obtain ⟨n, hframe, halign, h8, h9, hpc⟩ := width_runs s base width hc hp he ha hheader hs hwidth
  have hstable := hframe.small_stable
  have hlen : (r (.GPR 3#5) s).toNat = data.size := by
    have hl := hi.length
    change r (.GPR 3#5) s = BitVec.ofNat 64 data.size at hl
    rw [hl]
    exact Nat.mod_eq_of_lt (by have := hi.bounded; omega)
  rw [hlen] at hpc
  by_cases hm : width = data.size
  · have hpc' : read_pc (run n s) = base + 4320#64 := by simpa only [hm, ↓reduceIte] using hpc
    obtain ⟨m, t, hr, ht, htc, hte, hta, hti, hexit⟩ :=
      Small.trim_and_pack (run n s) base data (hstable.code hc) hpc'
        (hstable.err.trans he) halign (hstable.input hi)
    refine ⟨n+m, t, ?_, hstable.trans ht, htc, hte, hta, hti, ?_⟩
    · rw [run_plus, hr]
    · simpa only [PrefixExit, hm, ↓reduceIte] using hexit
  · refine ⟨n, run n s, rfl, hstable, hstable.code hc, hstable.err.trans he,
      halign, hstable.input hi, ?_⟩
    simp only [PrefixExit, hm, ↓reduceIte]
    exact ⟨by simpa only [hm, ↓reduceIte] using hpc, h8, h9⟩

end SszArm.UintCodec
