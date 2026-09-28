import SszX86.SerializeRun
import SszX86.MeasureProofs

namespace SszX86.Serialize
open SszNative SszNative.Serialize UintCodec

/-- Original private codec::serialize PC0 through its actual RET, for all seven
primitive descriptors and every value kind. Every premise describes original
inputs/ownership or the exact same Executable closure. Measurement is called
with retain=true; neither a Plan nor any output value is preinitialized. -/
theorem program_correct (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra) :
    Eventually (step e) (Post s desc value buffer address capacity used ra) (s, base) := by
  apply entry_runs e base closure.wrapper s owned.entry_stack_mapped
  apply eventually_trans (step e) _ _ _
    (BitVector.Mapping.retains_mapping e _ _
      (Measure.program_correct e (base + Int64.ofInt measureOffset) closure.measure
        closure.measure_helpers (measureState s base) desc value buffer address capacity used
        (base + 47).toBitVec true owned.measure_owned))
  rintro ⟨body, pc⟩ ⟨post, mapping⟩
  have anchors := measured_anchors post
  have returned := anchors.pc
  dsimp only at returned
  subst pc
  have before : BeforeEmit s base desc value buffer address capacity used ra body := {
    anchors := ⟨anchors.stack, anchors.result, anchors.rbp, anchors.descriptor,
      anchors.capacity, anchors.output, anchors.value, anchors.vectors⟩
    resources := owned.measured_resources post
    «mapped» := measured_mapping mapping
    output := owned.measured_output post
    frame := measured_frame post }
  apply after_measure_runs e base closure s body desc value buffer address capacity used ra owned before
  have plan : body.regs.rsp.toBitVec + 24 = (measureState s base).regs.rdi.toBitVec := by
    rw [anchors.stack, measureState_plan_pointer]
    simp only [wrapperSP, planPointer]
    bv_omega
  simpa only [plan, UInt64.toNat_toBitVec] using post.observed

/-- Exact native execution plus pinned semantic correspondence, retaining the
ordered resource alternatives rather than conflating them with SSZ rejection.
Post separately pins committed cursor/calls, error payload, borrowed bytes,
untouched output tail, original ABI, and the outcome-sensitive byte frame. -/
theorem program_refines (e : Executable) (base : Int64) (closure : ClosureAt e base)
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used ra : BitVec 64)
    (owned : Owned s base desc value buffer address capacity used ra) :
    Eventually (step e) (fun final =>
      Post s desc value buffer address capacity used ra final ∧
      (eraseResult ((written s desc value address capacity used).outcome.result.map
          (fun _ => (written s desc value address capacity used).writes)) =
          .ok (Ssz.serialize desc.erase value.erase) ∨
        (written s desc value address capacity used).outcome.result =
          .error (.arithmetic .scratchExhausted) ∨
        (written s desc value address capacity used).outcome.result = .error .outputTooSmall))
      (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (program_correct e base closure s desc value buffer address capacity used ra owned)
  intro final post
  exact ⟨post, serialize_refines desc value s.regs.r8.toNat
    (arenaState address capacity used) owned.physical⟩

end SszX86.Serialize
