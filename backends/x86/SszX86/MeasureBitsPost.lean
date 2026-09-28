import SszX86.MeasureBitsMemory

namespace SszX86.Measure.Bits
open SszNative SszNative.Serialize UintCodec

/-- Resource observations describe the already-executed state. Original input
ownership is recovered from the exact write frame, rather than assumed at exit. -/
theorem body_post_of_resources (s t : MachineData) (desc : Desc) (value : Value)
    (buffer address capacity used : BitVec 64)
    (owned : BodyOwned s desc value buffer address capacity used)
    (stack : t.regs.rsp = s.regs.rsp) (vectors : t.zmms = s.zmms)
    (observed : ResultAt (widthLoad t.dmem) s.regs.rbx.toNat
      (measure desc value (arenaState address capacity used)).result)
    (cursor : widthLoad t.dmem (s.regs.rcx.toNat + 16) 8 =
      some (measure desc value (arenaState address capacity used)).used)
    (header : widthLoad t.dmem s.regs.rcx.toNat 8 = some address.toNat ∧
      widthLoad t.dmem (s.regs.rcx.toNat + 8) 8 = some capacity.toNat)
    (calls : CallsAt (widthLoad t.dmem) (measure desc value (arenaState address capacity used)).calls)
    (frame : MemoryFrame s.dmem t.dmem
      (BodyWritable s (measure desc value (arenaState address capacity used))))
    (geometry : ∀ call ∈ (measure desc value (arenaState address capacity used)).calls,
      ∀ r, call.allocation = some r → address.toNat + used.toNat ≤ r.pointer ∧
        r.pointer + 8 * call.written.length ≤ address.toNat + capacity.toNat) :
    BodyPost s desc value buffer address capacity used t := by
  have kept := original_inputs s desc value buffer address capacity used owned t.dmem
    (frame_mono _ _ _ _ frame (by
      intro a written
      rcases written with result | allocation | ⟨allocated, cursorWrite⟩ | localWrite
      · exact Or.inl (resultWrites_span _ _ _ result)
      · obtain ⟨call, member, r, allocated, inside⟩ := allocation
        have bounds := geometry call member r allocated
        exact Or.inr (Or.inr (Or.inl
          (allocation_in_free address used capacity r.pointer (8 * call.written.length)
            bounds.1 bounds.2 a inside)))
      · exact Or.inr (Or.inl cursorWrite)
      · exact Or.inr (Or.inr (Or.inr localWrite))))
  exact ⟨stack, observed, cursor, header, calls, kept.1, kept.2, frame, vectors⟩

theorem vector_call_eq (expected : NatOperand) (bits : Packed) (arena : Delimited.ArenaState)
    (call : NatArithmetic.Outcome NatOperand)
    (member : call ∈ (measure (.bitVector expected) (.bits bits) arena).calls) :
    call = NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count := by
  by_cases same : expected.value = bits.count.toNat
  · simp only [Serialize.measure, same, ↓reduceIte, unchanged, List.not_mem_nil] at member
  · cases counted : (fromWide arena bits.count).result with
    | error reason =>
      simp only [Serialize.measure, same, ↓reduceIte, Serialize.bind, counted] at member
      change call ∈ [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] at member
      exact List.mem_singleton.mp member
    | ok actual =>
      simp only [Serialize.measure, same, ↓reduceIte, Serialize.bind, counted, unchanged,
        List.append_nil] at member
      change call ∈ [NatArithmetic.fromWide arena.base arena.capacity arena.used bits.count] at member
      exact List.mem_singleton.mp member

theorem vector_call_geometry (expected : NatOperand) (bits : Packed)
    (arena : Delimited.ArenaState) (call : NatArithmetic.Outcome NatOperand)
    (member : call ∈ (measure (.bitVector expected) (.bits bits) arena).calls)
    (r : Arena.Reservation) (allocated : call.allocation = some r) :
    arena.base + arena.used ≤ r.pointer ∧
    r.pointer + 8 * call.written.length ≤ arena.base + arena.capacity := by
  obtain rfl := vector_call_eq expected bits arena call member
  have geometry := wide_allocation_geometry _ _ _ _ r allocated
  rw [geometry.2.1]
  exact ⟨geometry.2.2.1, by simpa using geometry.2.2.2.1⟩

end SszX86.Measure.Bits
