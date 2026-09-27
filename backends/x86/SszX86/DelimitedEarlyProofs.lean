import SszX86.DelimitedMemory
import SszX86.DelimitedEntry
import SszX86.DelimitedScan
import SszX86.DelimitedEarly
import SszX86.DelimitedReturn
import SszX86.DelimitedRetain

namespace SszX86.Delimited
open UintCodec

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem entry_frame_trans {s t u : MachineData}
    (first : EntryFrame s t) (second : EntryFrame t u) : EntryFrame s u := by
  refine ⟨second.1.trans first.1, second.2.1.trans first.2.1, ?_⟩
  intro r hr
  exact (second.2.2 r hr).trans (first.2.2 r hr)

private theorem entry_frame_rax (s : MachineData) (value : UInt64) :
    EntryFrame s {s with regs := {s.regs with rax := value}} := by
  refine ⟨rfl, rfl, ?_⟩
  intro r hr
  cases r <;> simp_all [Reg64s.get64]

private theorem entry_frame_scan (s : MachineData) (i : Nat) (flags : StatusFlags) :
    EntryFrame s (scanState s i flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r hr
  cases r <;> simp_all [scanState, Reg64s.get64]

private theorem early_load_apart (m : DataMem) (out source : BitVec 64)
    (reason : BitVec 32) (count : Nat) (apart : Large.Disjoint source out count 76) :
    Mem.loadInt (earlyMem m out reason) source count = Mem.loadInt m source count := by
  apply memmove_loadInt_congr
  intro i hi
  apply early_frame
  intro j hj
  exact apart i hi j hj

private theorem early_memory_image (s t : MachineData) (frame : EntryFrame s t)
    (reason : BitVec 32) :
    (earlyReady t reason).dmem = earlyMem s.dmem s.regs.rdi.toBitVec reason := by
  have out : t.regs.rdi.toBitVec = s.regs.rdi.toBitVec := frame.2.2 .rdi (by decide)
  simp only [earlyReady, frame.1, out]

private theorem early_returned (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (frame : EntryFrame s t) (reason : BitVec 32) :
    Returned s ra (retState (earlyReady t reason), Int64.ofBitVec ra) := by
  have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := frame.2.2 .rsp (by decide)
  have apart : Large.Disjoint s.regs.rsp.toBitVec s.regs.rdi.toBitVec 8 76 :=
    Body.apart_bytes _ _ 8 76 h.return_bound h.output_bound h.output_return.symm
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame.2.1, ?_⟩
  · simp only [retState, earlyReady, UInt64.toBitVec_ofBitVec, sp]
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .rbx (by decide))
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .rbp (by decide))
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .r12 (by decide))
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .r13 (by decide))
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .r14 (by decide))
  · exact UInt64.toBitVec_inj.1 (frame.2.2 .r15 (by decide))
  · change Mem.loadInt (earlyReady t reason).dmem s.regs.rsp.toBitVec 8 = _
    rw [early_memory_image s t frame reason, early_load_apart _ _ _ _ _ apart]
    exact h.return_load

private theorem early_global_frame (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (frame : EntryFrame s t) (reason : BitVec 32) :
    Frame s (retState (earlyReady t reason)).dmem data none := by
  change Frame s (earlyReady t reason).dmem data none
  rw [early_memory_image s t frame reason]
  intro a outside _ _
  apply early_frame
  intro i hi
  exact Body.outside_byte s.regs.rdi.toBitVec a 76 i h.output_bound outside hi

private theorem early_cursor (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (frame : EntryFrame s t) (reason : BitVec 32) :
    widthLoad (retState (earlyReady t reason)).dmem (s.regs.r8.toNat + 16) 8 = some used.toNat := by
  have separated : Large.Disjoint s.regs.r8.toBitVec s.regs.rdi.toBitVec 24 76 :=
    Body.apart_bytes _ _ 24 76 h.header_bound h.output_bound h.header_output
  have apart : Large.Disjoint (s.regs.r8.toBitVec + 16#64) s.regs.rdi.toBitVec 8 76 := by
    intro i hi j hj
    rw [memmove_addr_add]
    exact separated (16+i) (by omega) j hj
  change widthLoad (earlyReady t reason).dmem (s.regs.r8.toNat + 16) 8 = _
  rw [early_memory_image s t frame reason]
  simp only [widthLoad, ← UInt64.toNat_toBitVec, width_address]
  rw [early_load_apart _ _ _ _ _ apart]
  have current : Mem.loadInt s.dmem (s.regs.r8.toBitVec + 16#64) 8 = some (used.toNat : Int) := by
    simpa only [BitVec.ofNat_eq_ofNat] using h.used_load
  rw [current]
  rfl

private theorem early_post (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (frame : EntryFrame s t) (kind : Ssz.Err) (reason : BitVec 32)
    (model : SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
      ⟨.error (.semantic kind), used.toNat, none⟩)
    (encoding : (kind = .emptyEncoding ∧ reason = 16#32) ∨
      (kind = .noDelimiter ∧ reason = 17#32) ∨ (kind = .trailingZeros ∧ reason = 18#32)) :
    Post s limit data address capacity used ra
      (retState (earlyReady t reason), Int64.ofBitVec ra) := by
  refine ⟨?_, ?_, early_returned s t limit data address capacity used ra h frame reason, ?_, ?_⟩
  · change SszNative.Delimited.ResultAt (widthLoad (earlyReady t reason).dmem) _ _ _ _ _
    rw [early_memory_image s t frame reason, model]
    rcases encoding with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals exact early_result s.dmem s.regs.rdi.toBitVec _ h.output_bound
  · simp only [model, SszNative.Delimited.Outcome.PreparedAt]
    intro ready impossible
    cases impossible
  · simpa only [model, SszNative.Delimited.Outcome.allocation, Option.bind_none] using
      early_global_frame s t limit data address capacity used ra h frame reason
  · simpa only [model] using early_cursor s t limit data address capacity used ra h frame reason

private theorem early_ret_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s t : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (frame : EntryFrame s t) (kind : Ssz.Err) (reason : BitVec 32)
    (model : SszNative.Delimited.run limit data ⟨address.toNat, capacity.toNat, used.toNat⟩ =
      ⟨.error (.semantic kind), used.toNat, none⟩)
    (encoding : (kind = .emptyEncoding ∧ reason = 16#32) ∨
      (kind = .noDelimiter ∧ reason = 17#32) ∨ (kind = .trailingZeros ∧ reason = 18#32)) :
    Eventually (step e) (Post s limit data address capacity used ra) (earlyReady t reason, base + 232) ∧
    Eventually (step e) (Post s limit data address capacity used ra) (earlyReady t reason, base + 662) := by
  have post := early_post s t limit data address capacity used ra h frame kind reason model encoding
  have sp : t.regs.rsp.toBitVec = s.regs.rsp.toBitVec := frame.2.2 .rsp (by decide)
  have loaded : Mem.loadInt (earlyReady t reason).dmem (earlyReady t reason).regs.rsp.toBitVec 8 =
      some (Int.ofBytes (wordBytes ra)) := by
    simpa only [earlyReady, retState, sp] using post.returned.returnSlot
  have exits := ret_runs e base hc (earlyReady t reason) ra _ loaded post
  exact ⟨exits.1, exits.2.1⟩

/-- All validation failures execute their real RET with the full shared-model
postcondition. Only a validated nonzero final byte reaches the framed body. -/
theorem validation_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limit : Option Nat) (data : Ssz.Bytes)
    (address capacity used ra : BitVec 64) (h : Owned s limit data address capacity used ra)
    (body : ∀ flags, 0 < data.size → data[data.size - 1]! ≠ 0 →
      Eventually (step e) (Post s limit data address capacity used ra)
        (byteState s data[data.size - 1]! flags, base + 22)) :
    Eventually (step e) (Post s limit data address capacity used ra) (s, base) := by
  apply entry_length e base hc
  intro firstFlags
  have flaggedFrame : EntryFrame s {s with status := firstFlags} :=
    ⟨rfl, rfl, fun _ _ => rfl⟩
  by_cases empty : data.size = 0
  · have zero : s.regs.rcx = 0 := by
      apply UInt64.toBitVec_inj.1
      have hn : s.regs.rcx.toBitVec.toNat = 0 := h.length.symm.trans empty
      simp only [UInt64.toBitVec_ofNat]
      bv_omega
    rw [ite_eq_left zero]
    apply empty_stores e base hc {s with status := firstFlags} h.output_mapped
    exact (early_ret_cps e base hc s _ limit data address capacity used ra h flaggedFrame
      .emptyEncoding 16#32
      (by simp only [SszNative.Delimited.run, SszNative.Delimited.validate, empty, ↓reduceIte])
      (Or.inl ⟨rfl, rfl⟩)).1
  · have positive : 0 < data.size := by omega
    have nonzero : s.regs.rcx ≠ 0 := by
      intro zero
      apply empty
      simpa only [zero, show (0 : UInt64).toNat = 0 by decide] using h.length
    rw [ite_eq_right nonzero]
    have lastRead : Mem.loadInt s.dmem
        (s.regs.rdx.toBitVec + s.regs.rcx.toBitVec - 1#64) 1 =
        some (data[data.size - 1]!.toNat : Int) := by
      have physical : data.size < 2^64 := by rw [h.length]; exact s.regs.rcx.toBitVec.isLt
      have lengthWord : s.regs.rcx.toBitVec = BitVec.ofNat 64 data.size := by
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt physical, UInt64.toNat_toBitVec]
          using h.length.symm
      have predecessor : s.regs.rdx.toBitVec + s.regs.rcx.toBitVec - 1#64 =
          s.regs.rdx.toBitVec + BitVec.ofNat 64 (data.size - 1) := by
        rw [lengthWord]
        bv_omega
      rw [predecessor]
      have lastWithin : data.size - 1 < data.size := by omega
      simpa only [getElem!_pos data (data.size - 1) lastWithin,
        Array.getElem?_eq_getElem lastWithin, Option.getD_some] using h.source (data.size - 1) lastWithin
    apply last_byte_cps e base hc {s with status := firstFlags} data[data.size - 1]! lastRead
    intro byteFlags
    by_cases finalZero : data[data.size - 1]! = 0
    · rw [ite_eq_left finalZero]
      apply scan_init_cps e base hc
      intro scanFlags
      have execute : Eventually (step e) (Post s limit data address capacity used ra)
          (scanState s 0 scanFlags, base + 240) := by
        apply scan_runs e base hc s data h.length h.source _ data.size 0 (by omega) scanFlags
        · intro allZero flags
          have zeros : SszNative.Delimited.scanZeros data = true := by
            apply Array.all_eq_true.mpr
            intro i hi
            have value := allZero i (Nat.zero_le i) hi
            simpa only [Array.getElem?_eq_getElem hi, Option.getD_some, beq_iff_eq] using value
          apply no_delimiter_cps e base hc
          apply zero_stores e base hc
            {scanState s data.size flags with regs := {(scanState s data.size flags).regs with rax := 17}}
            h.output_mapped
          exact (early_ret_cps e base hc s _ limit data address capacity used ra h
            (entry_frame_trans (entry_frame_scan s data.size flags)
              (entry_frame_rax (scanState s data.size flags) 17)) .noDelimiter _
            (by simp only [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
              finalZero, zeros, ↓reduceIte])
            (Or.inr (Or.inl ⟨rfl, by
              change (17 : UInt64).toBitVec.setWidth 32 = 17#32
              decide⟩))).2
        · intro witness i flags
          have zeros : SszNative.Delimited.scanZeros data = false := by
            apply Array.all_eq_false.mpr
            obtain ⟨j, _, hj, value⟩ := witness
            refine ⟨j, hj, ?_⟩
            simpa only [Array.getElem?_eq_getElem hj, Option.getD_some, beq_iff_eq] using value
          apply trailing_zeros_cps e base hc
          apply zero_stores e base hc
            {scanState s i flags with regs := {(scanState s i flags).regs with rax := 18}}
            h.output_mapped
          exact (early_ret_cps e base hc s _ limit data address capacity used ra h
            (entry_frame_trans (entry_frame_scan s i flags)
              (entry_frame_rax (scanState s i flags) 18)) .trailingZeros _
            (by simp only [SszNative.Delimited.run, SszNative.Delimited.validate, empty,
              finalZero, zeros, Bool.false_eq_true, ↓reduceIte])
            (Or.inr (Or.inr ⟨rfl, by
              change (18 : UInt64).toBitVec.setWidth 32 = 18#32
              decide⟩))).2
      simpa only [scanState, byteState, uint64_literal 0] using execute
    · rw [ite_eq_right finalZero]
      simpa only [byteState] using body byteFlags positive finalZero

end SszX86.Delimited
