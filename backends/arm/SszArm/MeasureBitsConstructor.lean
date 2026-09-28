import SszArm.MeasureBitsConstructorReturn

namespace SszArm.Measure.Bits.Constructor

open UintCodec (widthLoad)
open Delimited (MemoryFrame)

/-- Actual BL1912, the complete accepted fromU128 entry-to-RET execution, and
both original return continuations through the common real epilogue frontier. -/
theorem executes (s : ArmState) (base : BitVec 64)
    (space : Space s) (code : CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 1912#64) :
    ∃ fuel t, run fuel s = t ∧ Post s t base := by
  obtain ⟨fuel, u, calledRun, native, nextPC, program, platform⟩ :=
    Helpers.constructor_correct_frame s base code error aligned pc space.native
  have stack : r (.GPR 31#5) u = r (.GPR 31#5) s :=
    native.returned.sp.trans (Helpers.called_register _ _ _ _ (by decide))
  have output : r (.GPR 19#5) u = r (.GPR 19#5) s :=
    (native.returned.registers 19#5 (by decide) (by decide)).trans
      (Helpers.called_register _ _ _ _ (by decide))
  have uAligned : CheckSPAlignment u := by
    simpa only [CheckSPAlignment, state_simp_rules, stack] using aligned
  obtain ⟨extra, t, tailRun, tail⟩ := return_executes s u base space (code.congr program)
    native.returned.error uAligned nextPC native
  have callFrame : MemoryFrame (NatFromU128.writesFor s) s u := by
    intro address outside
    have after := native.frame address (by
      simpa only [Helpers.constructor_called_writes] using outside)
    exact after.trans (congrFun (Helpers.called_memory .constructWidth s base) address)
  have headerBound := space.native.header
  have r0 := Emit.frame_read_offset tail.frame (r (.GPR 4#5) s) 24 0 8 headerBound
    space.headerTail (by decide)
  have r8 := Emit.frame_read_offset tail.frame (r (.GPR 4#5) s) 24 8 8 headerBound
    space.headerTail (by decide)
  have r16 := Emit.frame_read_offset tail.frame (r (.GPR 4#5) s) 24 16 8 headerBound
    space.headerTail (by decide)
  simp only [BitVec.add_zero] at r0
  refine ⟨fuel + extra, t, by rw [run_plus, calledRun, tailRun], ?_, ?_, ?_, ?_⟩
  · refine ⟨tail.pc, tail.program.trans program, tail.error, tail.stack.trans stack,
      ?_, ?_, ?_, ?_⟩
    · simpa only [output] using tail.result
    · apply (callFrame.weaken (by
        intro span member
        exact List.mem_append.mpr (Or.inl member))).trans
        (tail.frame.weaken (by
          intro span member
          exact List.mem_append.mpr (Or.inr member)))
    · intro reg member
      have throughTail := tail.registers reg member
      by_cases isPlatform : reg = 18#5
      · subst reg
        exact throughTail.trans platform
      · have retained : 19 ≤ reg.toNat ∧ reg.toNat ≤ 30 ∧ reg ≠ 30#5 := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · contradiction
          all_goals decide
        exact throughTail.trans
          ((native.returned.registers reg retained.1 retained.2.1).trans
            (Helpers.called_register _ _ _ _ retained.2.2))
    · intro reg low high
      exact (tail.vectors reg low high).trans
        ((native.returned.vectors reg low high).trans
          (congrArg (fun word : BitVec 128 => word.setWidth 64)
            (Helpers.called_vectors .constructWidth s base reg)))
  · rw [r16]
    simpa only [Helpers.called_register .constructWidth s base 4#5 (by decide),
      Helpers.constructor_called_outcome] using native.cursor
  · have header := native.header
    simp only [Helpers.called_register .constructWidth s base 4#5 (by decide)] at header
    have baseRead : NatFromU128.addressWord (Helpers.called .constructWidth s base) =
        NatFromU128.addressWord s := by
      simp [NatFromU128.addressWord, Helpers.called, state_simp_rules]
    have capacityRead : NatFromU128.capacityWord (Helpers.called .constructWidth s base) =
        NatFromU128.capacityWord s := by
      simp [NatFromU128.capacityWord, Helpers.called, state_simp_rules]
    exact ⟨r0.trans (header.1.trans baseRead), r8.trans (header.2.trans capacityRead)⟩
  · intro reservation allocated
    have input := native.written reservation (by
      simpa only [Helpers.constructor_called_outcome] using allocated)
    simp only [Helpers.constructor_called_outcome] at input
    have buffer := Helpers.fromWide_buffer_owned (tailWrites s) (NatDivision.arenaOf s)
      (NatFromU128.wide s) space.native.storage space.freeTail reservation allocated
    have preserved := NatDivision.operand_at_preserved tail.frame
      (.large (BitVec.ofNat 64 reservation.pointer) (NatFromU128.outcome s).written) input buffer
    have member : SszNative.NatArithmetic.fromWide (NatDivision.arenaOf s).base
        (NatDivision.arenaOf s).capacity (NatDivision.arenaOf s).used (NatFromU128.wide s) ∈
        (SszNative.Serialize.fromWide (NatDivision.arenaOf s) (NatFromU128.wide s)).calls := by
      simp [SszNative.Serialize.fromWide]
    have bounds := (resource_fromWide (NatDivision.arenaOf s) (NatFromU128.wide s)).allocations
      _ member reservation allocated
    have count := fromWide_written_length (NatDivision.arenaOf s) (NatFromU128.wide s)
      reservation allocated
    have storage : (NatDivision.arenaOf s).base + (NatDivision.arenaOf s).capacity ≤ 2^64 :=
      space.native.storage
    have pointerBound : reservation.pointer < 2^64 := by omega
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pointerBound] using preserved.2.2.2

end SszArm.Measure.Bits.Constructor
