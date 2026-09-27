import SszArm.NatAddSmallCorrectReturn

namespace SszArm.NatAdd.SmallCorrect

open UintCodec SszNative

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Compose the proved arithmetic prefix with either its immediate return or
all real reservation guards, stores and return instructions. The root ownership
continues to describe the original operand pairs after X2/X4 have been loaded. -/
theorem finish_sum (s u : ArmState) (base : BitVec 64) (left right : NatOperand)
    (owned : Owned s left right) (hc : CodeAt s base)
    (he : read_err s = .None) (ha : CheckSPAlignment s)
    (hl : left.wordCount = 1) (hr : right.wordCount = 1)
    (prefixFuel : Nat) (execution : run prefixFuel s = u) (prefix : ZeroFrame s u)
    (h5 : r (.GPR 5#5) u = r (.GPR 5#5) s)
    (h9 : r (.GPR 9#5) u = low left right)
    (hp : read_pc u = base +
      (if 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat + (SszNative.NatAdd.lowWord right).toNat
       then 1112#64 else 1004#64)) :
    ∃ fuel t, run fuel s = t ∧ Post s t left right := by
  by_cases overflow : 2^64 ≤ (SszNative.NatAdd.lowWord left).toNat +
      (SszNative.NatAdd.lowWord right).toNat
  · have up : read_pc u = base + 1112#64 := by simpa only [overflow, ↓reduceIte] using hp
    let address := read_mem_bytes 8 (r (.GPR 5#5) s) s
    let capacity := read_mem_bytes 8 (r (.GPR 5#5) s + 8#64) s
    let used := read_mem_bytes 8 (r (.GPR 5#5) s + 16#64) s
    have headerBase : read_mem_bytes 8 (r (.GPR 5#5) u) u = address := by
      simpa only [BitVec.ofNat_zero, BitVec.add_zero] using prefix_header owned prefix h5 0 (by decide)
    have headerCapacity : read_mem_bytes 8 (r (.GPR 5#5) u + 8#64) u = capacity :=
      prefix_header owned prefix h5 8 (by decide)
    have headerUsed : read_mem_bytes 8 (r (.GPR 5#5) u + 16#64) u = used :=
      prefix_header owned prefix h5 16 (by decide)
    obtain ⟨reserveFuel, v, executed, arenaFrame, result⟩ :=
      arena_small_reservation_runs u base address capacity used
        (prefix.code hc) (prefix.error.trans he) (prefix.aligned ha) up
        headerBase headerCapacity headerUsed (by
          intro reservation reserved
          apply reservation_owned owned hl hr overflow h5 reservation
          exact reserved)
    rcases result with ⟨failed, vp, memory⟩ | ⟨reservation, reserved, success⟩
    · have model : outcome s left right =
          NatArithmetic.unchanged (arenaOf s).used (.error .scratchExhausted) := by
        rw [model_overflow s left right hl hr overflow]
        change (match Arena.reserve address.toNat capacity.toNat used.toNat 2 with
          | none => _ | some reservation => _) = _
        rw [failed]
      obtain ⟨tailFuel, t, runTail, post⟩ := error_finish s v base left right owned
        (prefix_trans prefix (arena_prefix arenaFrame memory))
        (arenaFrame.code base (prefix.code hc)) (arenaFrame.error.trans (prefix.error.trans he))
        (arenaFrame.aligned (prefix.aligned ha)) vp model
      refine ⟨prefixFuel + reserveFuel + tailFuel, t, ?_, post⟩
      rw [run_plus, run_plus, execution, executed, runTail]
    · obtain ⟨tailFuel, t, runTail, post⟩ := allocated_finish s u v base left right
        owned prefix h5 h9 hl hr overflow reservation reserved arenaFrame success
        (arenaFrame.code base (prefix.code hc)) (arenaFrame.error.trans (prefix.error.trans he))
        (arenaFrame.aligned (prefix.aligned ha))
      refine ⟨prefixFuel + reserveFuel + tailFuel, t, ?_, post⟩
      rw [run_plus, run_plus, execution, executed, runTail]
  · have up : read_pc u = base + 1004#64 := by simpa only [overflow, ↓reduceIte] using hp
    have finish : ZeroRun u (.small (low left right)) :=
      value_zero_run .small u base (prefix.code hc) (prefix.error.trans he)
        (prefix.aligned ha) up (prefix.owned owned.return_owned) (.small (low left right))
        rfl h9 trivial trivial
    exact (ZeroRun.prepend prefixFuel execution prefix finish).post owned
      (model_small s left right hl hr overflow)

end SszArm.NatAdd.SmallCorrect
