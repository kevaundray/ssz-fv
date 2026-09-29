import SszX86.CodecSerializeOwned
import SszX86.SerializeMeasureOwned

namespace SszX86.CodecSerialize
open SszNative UintCodec

/-- Any actual wrapper window fits its complete recursive stack allowance. -/
theorem stack_window (s : MachineData) (desc : SszNative.Codec.Desc)
    (distance count : Nat) (fits : count ≤ distance) (within : distance ≤ stackBytes desc)
    {a : BitVec 64}
    (inside : Codec.InSpan a (s.regs.rsp.toBitVec - BitVec.ofNat 64 distance) count) :
    Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc) a := by
  obtain ⟨i, hi, rfl⟩ := inside
  refine ⟨stackBytes desc - distance + i, by omega, ?_⟩
  bv_omega

theorem stackBytes_wrapper (desc : SszNative.Codec.Desc) : 144 ≤ stackBytes desc := by
  unfold stackBytes
  omega

theorem Owned.stack_window_mapped {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra)
    (distance count : Nat) (fits : count ≤ distance) (within : distance ≤ stackBytes desc) :
    Large.Mapped s.dmem (s.regs.rsp.toBitVec - BitVec.ofNat 64 distance) count := by
  have hmap := Delimited.Reservation.mapped_subrange s.dmem (stackBase s desc)
    (stackBytes desc) (stackBytes desc - distance) count owned.stack.mapped (by omega)
  have pointer : stackBase s desc + BitVec.ofNat 64 (stackBytes desc - distance) =
      s.regs.rsp.toBitVec - BitVec.ofNat 64 distance := by
    unfold stackBase
    bv_omega
  rwa [pointer] at hmap

theorem measure_frame_stack (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc) :
    Codec.MemoryFrame s.dmem (Serialize.measureState s base).dmem
      (Codec.StackWrites s.regs.rsp.toBitVec (stackBytes desc)) := by
  intro a outside
  apply Serialize.measureState_frame s base a
  rintro (saved | call)
  · exact outside (stack_window s desc 40 40 (by decide)
      (by have := stackBytes_wrapper desc; omega) saved)
  · exact outside (stack_window s desc 144 8 (by decide) (stackBytes_wrapper desc) call)

theorem measure_bottom (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc) :
    (Serialize.measureState s base).regs.rsp.toBitVec - BitVec.ofNat 64 (CodecMeasure.stackBytes desc) =
      stackBase s desc := by
  rw [Serialize.measureState_stack_pointer]
  unfold stackBase stackBytes
  bv_omega

theorem Owned.measure_stack_nat {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    (Serialize.measureState s base).regs.rsp.toNat = s.regs.rsp.toNat - 144 := by
  have low : 144 ≤ s.regs.rsp.toNat := (stackBytes_wrapper desc).trans owned.stack.lowEnough
  simp only [← UInt64.toNat_toBitVec] at low ⊢
  rw [Serialize.measureState_stack_pointer]
  bv_omega

theorem Owned.plan_pointer_nat {s : MachineData} {base : Int64}
    {desc : SszNative.Codec.Desc} {value : SszNative.Codec.Value} {readonly : Codec.Footprint}
    {address capacity used ra : BitVec 64}
    (owned : Owned s base desc value readonly address capacity used ra) :
    (planPointer s).toNat = s.regs.rsp.toNat - 112 := by
  have low : 144 ≤ s.regs.rsp.toNat := (stackBytes_wrapper desc).trans owned.stack.lowEnough
  simp only [← UInt64.toNat_toBitVec] at low ⊢
  unfold planPointer
  bv_omega

theorem measure_available (s : MachineData) (base : Int64) (desc : SszNative.Codec.Desc)
    (address capacity used a : BitVec 64)
    (writes : CodecMeasure.Available (Serialize.measureState s base) desc address capacity used a) :
    Available s desc address capacity used a := by
  simp only [CodecMeasure.Available, Serialize.measureState_plan_pointer,
    Serialize.measureState_arena_pointer, Serialize.planPointer] at writes
  rcases writes with plan | header | arena | activation
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    exact stack_window s desc 112 72 (by decide)
      (by have := stackBytes_wrapper desc; omega) plan
  · exact Or.inr (Or.inr (Or.inl header))
  · exact Or.inr (Or.inr (Or.inr (Or.inl arena)))
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    rw [Serialize.measureState_stack_pointer] at activation
    exact Codec.stack_subspan s.regs.rsp.toBitVec 144 (CodecMeasure.stackBytes desc)
      (stackBytes desc) (by rfl) a activation

end SszX86.CodecSerialize
