import SszArm.ByteViewVectorBody
import SszArm.ByteViewListWidth

namespace SszArm.ByteView.Bounded

open UintCodec (widthLoad)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Complete arbitrary-Nat ByteList decoding through the original RET, with
exact Limit errors and an unchanged, originally aliased successful byte view. -/
theorem runs (s : ArmState) (base : BitVec 64) (capacity : Nat) (data : Ssz.Bytes)
    (hc : CodeAt s base) (hp : read_pc s = base + 688#64)
    (he : read_err s = .None) (ha : CheckSPAlignment s) (ho : Owned s capacity data) :
    ∃ fuel t, run fuel s = t ∧ Result s t (Ssz.deserialize (.byteList capacity) data) data := by
  obtain ⟨fuel, hf, halign, h8, h9, hpc⟩ := width_runs s base capacity hc hp he ha
    ho.descriptorHigh ho.scratch ho.width_at
  let t := run fuel s
  change UintCodec.WidthFrame s t at hf
  change CheckSPAlignment t at halign
  change r (.GPR 8#5) t = _ at h8
  change r (.GPR 9#5) t = _ at h9
  change read_pc t = _ at hpc
  have htc : CodeAt t base := by simpa only [CodeAt, hf.program] using hc
  have hte : read_err t = .None := hf.error.trans he
  have h0 : r (.GPR 0#5) t = r (.GPR 0#5) s := hf.registers 0#5 (by decide)
  have h2 : r (.GPR 2#5) t = r (.GPR 2#5) s := hf.registers 2#5 (by decide)
  have h3 : r (.GPR 3#5) t = r (.GPR 3#5) s := hf.registers 3#5 (by decide)
  have hn : Tail.NatPair t (r (.GPR 8#5) t) (r (.GPR 9#5) t) capacity := by
    rw [h8, h9]
    exact hf.bytePair _ _ _ ho.pair
  rw [← SszNative.ByteView.list_outcome_eq_deserialize]
  by_cases hm : data.size ≤ capacity
  · have htp : read_pc t = base + 4492#64 := by
      simpa only [ho.input.size, hm, ↓reduceIte] using hpc
    obtain ⟨hr, herr, hresult, halias⟩ := Tail.success_correct t base data htc htp hte
      halign (hf.byteSeparated ho.separated) (hf.byteInput ho.input)
    refine ⟨fuel + 21, run 21 t, by rw [run_plus], ?_⟩
    apply result_of_returned ho (hf.byteReturned ho.separated hr) herr
    · simpa only [SszNative.ByteView.listOutcome, hm, ↓reduceIte, h0] using hresult
    · intro _
      simpa only [h0, h2] using halias
  · have htp : read_pc t = base + 3576#64 := by
      simpa only [ho.input.size, hm, ↓reduceIte] using hpc
    obtain ⟨hr, herr, hresult⟩ := Tail.limit_correct t base capacity htc htp hte
      halign (hf.byteSeparated ho.separated) hn
    refine ⟨fuel + 48, run 48 t, by rw [run_plus], ?_⟩
    apply result_of_returned ho (hf.byteReturned ho.separated hr) herr
    · simpa only [SszNative.ByteView.listOutcome, hm, ↓reduceIte, h0, h3, ho.input.size] using hresult
    · simp [SszNative.ByteView.listOutcome, hm]

end SszArm.ByteView.Bounded
