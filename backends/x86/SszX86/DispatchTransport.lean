import SszX86.DispatchNat
import SszX86.ByteViewBody

namespace SszX86.Dispatch
open SszNative UintCodec BoolCodec

@[simp] theorem body_output (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.rdi = s.regs.rdi := rfl
@[simp] theorem body_descriptor (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.rbp = s.regs.rsi := rfl
@[simp] theorem body_source (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.rdx = s.regs.rdx := rfl
@[simp] theorem body_length (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.r14 = s.regs.rcx := rfl
@[simp] theorem body_arena (s : MachineData) (base : Int64) (kind : Kind) :
    (bodyState s base kind).regs.rbx = s.regs.r8 := rfl

variable {s : MachineData} {base : Int64} {kind : Kind} {ra : BitVec 64}
  {data : Ssz.Bytes} {address capacity used : BitVec 64}

theorem Owned.saved_at (h : Owned s base kind ra data address capacity used) :
    SavedAt (bodyState s base kind).dmem (bodyState s base kind).regs.rsp.toBitVec (saved s ra) := by
  rw [body_memory, body_sp]
  exact Dispatch.saved_at s ra h.return_load

theorem Owned.stack_mapping (h : Owned s base kind ra data address capacity used)
    (off n : Nat) (within : off + n ≤ 480) :
    Large.Mapped (savedMem s) (s.regs.rsp.toBitVec - 472 + BitVec.ofNat 64 off) n := by
  have hm := saved_mapped s _ _ h.stack_mapped
  intro i hi
  have byte := hm (off + i) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using byte

theorem Owned.source_bytes (h : Owned s base kind ra data address capacity used) :
    Large.BytesAt (savedMem s) s.regs.rdx.toBitVec data := by
  intro i hi
  have same := (h.source_owned.subrange i 1 (by omega)).load h.stack_low
  simp only [← UInt64.toNat_toBitVec, width_address] at same
  rw [same]
  exact h.source i hi

theorem Owned.source_view (h : Owned s base kind ra data address capacity used) :
    SszNative.ByteView.BytesAt (widthLoad (savedMem s)) s.regs.rdx.toNat data := by
  intro i hi
  have stored := h.source_bytes i hi
  simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address, stored,
    Option.map_some, Int.toNat_natCast]

theorem Owned.header_load (h : Owned s base kind ra data address capacity used)
    (off : Nat) (within : off + 8 ≤ 24) :
    Mem.loadInt (savedMem s) (s.regs.r8.toBitVec + BitVec.ofNat 64 off) 8 =
      Mem.loadInt s.dmem (s.regs.r8.toBitVec + BitVec.ofNat 64 off) 8 := by
  apply saved_load
  intro i hi j hj
  have bound := h.header_bound
  have apart := h.header_stack
  have low := h.stack_low
  clear h
  change s.regs.r8.toBitVec.toNat + 24 ≤ 2^64 at bound
  change Body.Apart s.regs.r8.toBitVec.toNat 24
    (s.regs.rsp.toBitVec.toNat - 472) 480 at apart
  change 472 ≤ s.regs.rsp.toBitVec.toNat at low
  unfold Body.Apart at apart
  bv_omega

theorem ReadOnly.uint {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) :
    Body.Protected (bodyState s base kind) address capacity used p n := by
  refine ⟨h.bound, ?_, ?_, ?_, h.arena⟩
  · have apart := h.output
    have outputRegion : Body.Apart p n s.regs.rdi.toNat 76 := by
      unfold Body.Apart at apart ⊢
      omega
    exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n r.toNat 76)
      (body_output s base kind)) outputRegion
  · have apart : Body.Apart p n (s.regs.rsp.toNat - 472) 472 := h.stack
    have workRegion : Body.Apart p n (s.regs.rsp.toNat - 360 + 120) 48 := by
      unfold Body.Apart at apart ⊢
      omega
    exact Eq.mpr (congrArg (fun q : Nat => Body.Apart p n (q + 120) 48)
      (body_spNat s base kind low)) workRegion
  · exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n (r.toNat + 16) 8)
      (body_arena s base kind)) h.cursor

theorem ReadOnly.byteView {p n : Nat} (h : ReadOnly s address capacity used p n) :
    SszX86.ByteView.Protected (bodyState s base kind) p n := by
  refine ⟨h.bound, ?_⟩
  change Body.Apart p n s.regs.rdi.toNat 76
  have apart := h.output
  unfold Body.Apart at *
  omega

theorem ReadOnly.bitVector {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) :
    SszX86.BitVector.Protected (bodyState s base kind) address capacity used p n := by
  refine ⟨h.bound, ?_, ?_, ?_, h.arena⟩
  · exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n r.toNat 80)
      (body_output s base kind)) h.output
  · have apart : Body.Apart p n (s.regs.rsp.toNat - 472) 472 := h.stack
    have workRegion : Body.Apart p n (s.regs.rsp.toNat - 360 - 72) 296 := by
      unfold Body.Apart at apart ⊢
      omega
    change Body.Apart p n ((bodyState s base kind).regs.rsp.toNat - 72) 296
    exact Eq.mpr (congrArg (fun q : Nat => Body.Apart p n (q - 72) 296)
      (body_spNat s base kind low)) workRegion
  · exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n (r.toNat + 16) 8)
      (body_arena s base kind)) h.cursor

theorem ReadOnly.bitList {p n : Nat} (h : ReadOnly s address capacity used p n)
    (low : 472 ≤ s.regs.rsp.toNat) (tail : Bool) :
    SszX86.BitList.Protected (bodyState s base kind) tail address capacity used p n := by
  refine ⟨h.bound, ?_, ?_, ?_, h.arena⟩
  · exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n r.toNat 80)
      (body_output s base kind)) h.output
  · have apart : Body.Apart p n (s.regs.rsp.toNat - 472) 472 := h.stack
    have workRegion : Body.Apart p n
        (if tail then s.regs.rsp.toNat - 360 + 256 else s.regs.rsp.toNat - 360 - 112)
        (if tail then 104 else 152) := by
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
        unfold Body.Apart at apart ⊢ <;> omega
    change Body.Apart p n
      (if tail then (bodyState s base kind).regs.rsp.toNat + 256
        else (bodyState s base kind).regs.rsp.toNat - 112) (if tail then 104 else 152)
    exact Eq.mpr (congrArg (fun q : Nat => Body.Apart p n
      (if tail then q + 256 else q - 112) (if tail then 104 else 152))
      (body_spNat s base kind low)) workRegion
  · exact Eq.mpr (congrArg (fun r : UInt64 => Body.Apart p n (r.toNat + 16) 8)
      (body_arena s base kind)) h.cursor

theorem Owned.tail (h : Owned s base kind ra data address capacity used) :
    Body.TailOwned (bodyState s base kind) (saved s ra) := by
  have sp := body_spNat s base kind h.stack_low
  refine ⟨saved_mapped s _ _ h.output_mapped, ?_, h.saved_at, ?_⟩
  · change Large.Mapped (savedMem s) (bodyState s base kind).regs.rsp.toBitVec 368
    rw [body_sp]
    have hm := h.stack_mapping 112 368 (by decide)
    have addr : s.regs.rsp.toBitVec - 472 + BitVec.ofNat 64 112 =
        s.regs.rsp.toBitVec - 360 := by bv_omega
    rw [addr] at hm
    exact hm
  · refine ⟨h.output_bound, ?_, ?_⟩
    · change (bodyState s base kind).regs.rsp.toNat + 368 ≤ 2^64
      have stackBound : s.regs.rsp.toNat - 360 + 368 ≤ 2^64 := by
        have := h.stack_bound
        have := h.stack_low
        omega
      exact Eq.mpr (congrArg (fun q : Nat => q + 368 ≤ 2^64) sp) stackBound
    · change s.regs.rdi.toNat + 80 ≤ (bodyState s base kind).regs.rsp.toNat ∨
        (bodyState s base kind).regs.rsp.toNat + 368 ≤ s.regs.rdi.toNat
      have apart : Body.Apart s.regs.rdi.toNat 80 (s.regs.rsp.toNat - 472) 480 :=
        h.output_stack
      have low := h.stack_low
      have separated : s.regs.rdi.toNat + 80 ≤ s.regs.rsp.toNat - 360 ∨
          s.regs.rsp.toNat - 360 + 368 ≤ s.regs.rdi.toNat := by
        unfold Body.Apart at apart
        omega
      exact Eq.mpr (congrArg (fun q : Nat => s.regs.rdi.toNat + 80 ≤ q ∨
        q + 368 ≤ s.regs.rdi.toNat) sp) separated

end SszX86.Dispatch
