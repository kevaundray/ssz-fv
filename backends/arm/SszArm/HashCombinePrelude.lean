import SszArm.HashCombineEntry
import SszArm.HashCombineDirect
import SszArm.HashGeometry
import SszArm.HashCombineMetadata

namespace SszArm.Hash.Combine

open Delimited (Span Protected MemoryFrame)

def saveMemory (s : ArmState) : ArmState :=
  write_mem_bytes 16 (bodySP s + 288#64) (r (.GPR 19#5) s ++ r (.GPR 20#5) s)
  (write_mem_bytes 16 (bodySP s + 272#64) (r (.GPR 21#5) s ++ r (.GPR 22#5) s)
  (write_mem_bytes 16 (bodySP s + 256#64) (r (.GPR 23#5) s ++ r (.GPR 24#5) s)
  (write_mem_bytes 16 (bodySP s + 240#64) (r (.GPR 25#5) s ++ r (.GPR 30#5) s)
  (write_mem_bytes 8 (bodySP s + 224#64) (r (.GPR 29#5) s) s))))

private theorem saved_store_memory (s : ArmState) (count : Nat)
    (address : BitVec 64) (value : BitVec (count * 8)) :
    (write_mem_bytes count address value s).mem =
      Memory.write_bytes count address value s.mem := by
  simp only [Memory.write_mem_bytes_eq_mem_write_bytes]

theorem saveEntry_memory (s : ArmState) : (saveEntry s).mem = (saveMemory s).mem := by
  simp [saveEntry, saveOps, block, Op.effect, put, store, save, next,
    saveMemory, bodySP, state_simp_rules]
  simp only [saved_store_memory, ArmState.mem_w_eq_mem]

theorem saveEntry_frame (s : ArmState) (low : 496 ≤ (r (.GPR 31#5) s).toNat) :
    MemoryFrame (combineWrites s) s (saveEntry s) := by
  intro address outside
  have apart := outside (stackSpan s 496) (by simp [combineWrites])
  simp only [stackSpan] at apart
  rw [saveEntry_memory]
  simp only [saveMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ _ _ address
    (by simp only [bodySP]; bv_omega) (by simp only [bodySP]; bv_omega)]

theorem saveEntry_saved (s : ArmState) (low : 496 ≤ (r (.GPR 31#5) s).toNat) :
    Saved s (saveEntry s) := by
  have reads := Memory.mem_eq_iff_read_mem_bytes_eq.mp (saveEntry_memory s)
  constructor
  · rw [saveEntry_sp, reads]
    simp (disch := (simp only [bodySP]; bv_omega)) only [saveMemory,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · rw [saveEntry_sp, reads]
    simp (disch := (simp only [bodySP]; bv_omega)) only [saveMemory,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · rw [saveEntry_sp, reads]
    simp (disch := (simp only [bodySP]; bv_omega)) only [saveMemory,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · rw [saveEntry_sp, reads]
    simp (disch := (simp only [bodySP]; bv_omega)) only [saveMemory,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · rw [saveEntry_sp, reads]
    simp (disch := (simp only [bodySP]; bv_omega)) only [saveMemory,
      BoolCodec.read_mem_bytes_write_mem_bytes_same,
      BoolCodec.read_mem_bytes_write_mem_bytes_disjoint]
  · exact saveEntry_register s 26#5 (by decide)
  · exact saveEntry_register s 27#5 (by decide)
  · exact saveEntry_register s 28#5 (by decide)
  · intro reg lo hi
    simp [saveEntry, saveOps, block, Op.effect, put, store, save, next, state_simp_rules]

theorem initialize_sp (s : ArmState) : r (.GPR 31#5) (initializeState s) = r (.GPR 31#5) s := by
  simp [initializeState, initializeOps, block, Op.effect, put, next, state_simp_rules]

theorem initialize_saved_register (s : ArmState) (reg : BitVec 5)
    (lo : 26 ≤ reg.toNat) (hi : reg.toNat ≤ 28) :
    r (.GPR reg) (initializeState s) = r (.GPR reg) s := by
  have different : reg ≠ 0#5 ∧ reg ≠ 1#5 ∧ reg ≠ 2#5 ∧ reg ≠ 19#5 ∧
      reg ≠ 20#5 ∧ reg ≠ 21#5 ∧ reg ≠ 22#5 ∧ reg ≠ 23#5 ∧ reg ≠ 24#5 := by bv_omega
  simp [initializeState, initializeOps, block, Op.effect, put, next, state_simp_rules, different]

theorem initialize_vector (s : ArmState) (reg : BitVec 5) (nonzero : reg ≠ 0#5) :
    r (.SFP reg) (initializeState s) = r (.SFP reg) s := by
  simp [initializeState, initializeOps, block, Op.effect, put, next, state_simp_rules, nonzero]

theorem initialize_frame (s : ArmState)
    (physical : (r (.GPR 31#5) s).toNat + 64 ≤ 2^64) :
    MemoryFrame [((r (.GPR 31#5) s).toNat, 64)] s (initializeState s) := by
  intro address outside
  have apart := outside ((r (.GPR 31#5) s).toNat, 64) (by simp)
  rw [initialize_memory]
  rw [BoolCodec.write_mem_bytes_frame _ _ 32 _ address (by bv_omega) (by bv_omega),
    BoolCodec.write_mem_bytes_frame _ _ 32 _ address (by bv_omega) (by bv_omega)]

structure PreludePost (origin t : ArmState) (base : BitVec 64) (left right : ByteArray) : Prop where
  pc : read_pc t = if left.size / 64 = 0 then base + 160#64 else base + 132#64
  error : read_err t = .None
  program : t.program = origin.program
  aligned : CheckSPAlignment t
  sp : r (.GPR 31#5) t = bodySP origin
  x19 : r (.GPR 19#5) t = r (.GPR 0#5) origin
  x20 : r (.GPR 20#5) t = r (.GPR 4#5) origin
  x21 : r (.GPR 21#5) t = r (.GPR 3#5) origin
  x22 : r (.GPR 22#5) t = r (.GPR 2#5) origin
  x23 : r (.GPR 23#5) t = r (.GPR 1#5) origin
  x24 : r (.GPR 24#5) t = r (.GPR 31#5) t
  saved : Saved origin t
  state : StateAt t (r (.GPR 31#5) t)
    { SszNative.HashStream.new with byteLen := UInt64.ofNat left.size }
  frame : MemoryFrame (combineWrites origin) origin t

structure Initialized (origin t : ArmState) (base : BitVec 64) : Prop where
  pc : read_pc t = base + 80#64
  error : read_err t = .None
  program : t.program = origin.program
  aligned : CheckSPAlignment t
  sp : r (.GPR 31#5) t = bodySP origin
  x19 : r (.GPR 19#5) t = r (.GPR 0#5) origin
  x20 : r (.GPR 20#5) t = r (.GPR 4#5) origin
  x21 : r (.GPR 21#5) t = r (.GPR 3#5) origin
  x22 : r (.GPR 22#5) t = r (.GPR 2#5) origin
  x23 : r (.GPR 23#5) t = r (.GPR 1#5) origin
  x24 : r (.GPR 24#5) t = r (.GPR 31#5) t
  saved : Saved origin t
  buffer : BytesAt t (r (.GPR 31#5) t) ⟨SszNative.HashStream.new.buffer.toArray⟩
  chaining : ChainingAt t (r (.GPR 31#5) t + 64#64) Ssz.Sha256.initialState
  frame : MemoryFrame (combineWrites origin) origin t

theorem initialized_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (pc : read_pc s = base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    Initialized s (run (19 + (Memcpy.fuel 32 + 1)) s) base := by
  have low := owned.stackLow
  have spNat : (bodySP s).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    simp only [bodySP]; bv_omega
  have bodyPhysical : (bodySP s).toNat + 304 ≤ 2^64 := by
    have upper := (r (.GPR 31#5) s).isLt
    rw [spNat]; omega
  let a := saveEntry s
  let b := initializeState a
  let c := run (Memcpy.fuel 32 + 1) b
  have aSP : r (.GPR 31#5) a = bodySP s := saveEntry_sp s
  have aPC : read_pc a = base + 24#64 := by rw [saveEntry_pc, pc]
  have aCode := code.of_program_eq (saveEntry_program s)
  have aError := (saveEntry_error s).trans error
  have aAligned : CheckSPAlignment a := saveEntry_aligned s aligned
  have aFrame := saveEntry_frame s low
  have aSaved : Saved s a := saveEntry_saved s low
  obtain ⟨bPC, b0, b1, b2, b19, b20, b21, b22, b23, b24⟩ :=
    initialize_arguments a base aPC
  change read_pc b = base + 76#64 at bPC
  change r (.GPR 0#5) b = r (.GPR 31#5) a + 64#64 at b0
  change r (.GPR 1#5) b = base + initialOffset at b1
  change r (.GPR 2#5) b = 32#64 at b2
  have bSP : r (.GPR 31#5) b = bodySP s := (initialize_sp a).trans aSP
  have bProgram : b.program = s.program := (initialize_program a).trans (saveEntry_program s)
  have bCode := code.of_program_eq bProgram
  have bError : read_err b = .None := (initialize_error a).trans aError
  have bAligned : CheckSPAlignment b := by
    simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, bSP, aSP] using aAligned
  have bufferFrame := initialize_frame a (by rw [aSP]; omega)
  have bFrame : MemoryFrame (combineWrites s) s b := aFrame.trans (frame_mono bufferFrame (by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, aSP, spNat] <;> omega))
  have bData : DataAt b base := data.frame bFrame owned.initialOwned owned.roundsOwned
  have bSaved : Saved s b := aSaved.of_frame bufferFrame (by rw [aSP]; exact bodyPhysical)
    (by
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rw [aSP]
      bv_omega)
    (initialize_sp a) (initialize_saved_register a)
    (by intro reg lo hi; rw [initialize_vector a reg (by bv_omega)])
  have bLength : (r (.GPR 2#5) b).toNat = 32 := by rw [b2]; rfl
  have bDestination : (r (.GPR 0#5) b).toNat + 32 ≤ 2^64 := by rw [b0, aSP]; bv_omega
  have bSource : (r (.GPR 1#5) b).toNat + 32 ≤ 2^64 := by rw [b1]; exact data.initialBound
  have tableApart : (base + initialOffset).toNat + 32 ≤ (r (.GPR 31#5) s).toNat - 496 ∨
      (r (.GPR 31#5) s).toNat ≤ (base + initialOffset).toNat := by
    rcases owned.initialOwned with empty | separate
    · omega
    · have apart := separate (stackSpan s 496) (by simp [combineWrites])
      simp only [stackSpan] at apart
      omega
  have separation : Memcpy.Disjoint (r (.GPR 0#5) b) (r (.GPR 1#5) b) 32 := by
    rw [b0, b1, aSP]
    unfold Memcpy.Disjoint
    bv_omega
  have copied := copy_correct .initial b base bCode bPC bError bAligned
    (by rw [bLength]; exact bDestination) (by rw [bLength]; exact bSource)
    (by rw [bLength]; exact separation)
  rw [bLength] at copied
  have cSP : r (.GPR 31#5) c = bodySP s :=
    (copied.registers 31#5 (by decide)).trans bSP
  have cFrame : MemoryFrame (combineWrites s) s c := bFrame.trans (frame_mono copied.frame (by
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
      simp only [stackSpan, b0, aSP, bLength] <;> bv_omega))
  have cSaved : Saved s c := bSaved.of_frame copied.frame (by rw [bSP]; exact bodyPhysical)
    (by
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rw [bSP, b0, aSP, bLength]
      bv_omega)
    (copied.registers 31#5 (by decide))
    (by intro reg lo hi; exact copied.registers reg (by simp; bv_omega))
    (by intro reg lo hi; rw [copied.vectors reg (by bv_omega)])
  have buffer : BytesAt c (bodySP s) ⟨SszNative.HashStream.new.buffer.toArray⟩ := by
    apply bytesAt_frame copied.frame
    · rw [vectorByteArray_size]; omega
    · rw [vectorByteArray_size]
      right
      intro span member
      simp only [List.mem_singleton] at member
      subst span
      rw [b0, aSP, bLength]
      bv_omega
    · simpa only [aSP] using initialize_buffer a (by rw [aSP]; omega)
  have chaining : ChainingAt c (bodySP s + 64#64) Ssz.Sha256.initialState := by
    apply initial_copy (s := b) (src := base + initialOffset)
    · exact bData.initial
    · intro address
      simpa only [b0, b1, aSP, bLength] using copied.memory address
    · bv_omega
    · exact data.initialBound
  have execution : run (19 + (Memcpy.fuel 32 + 1)) s = c := by
    rw [run_plus]
    have first : run 19 s = b := by
      change run (6 + 13) s = b
      rw [run_plus, saveEntry_run s base code error aligned pc,
        initialize_run a base aCode aError aAligned aPC]
    rw [first]
  rw [execution]
  refine ⟨?_, copied.error, copied.program.trans bProgram, ?_, cSP, ?_, ?_, ?_, ?_, ?_, ?_,
    cSaved, ?_, ?_, cFrame⟩
  · rw [copied.pc, bPC]; bv_omega
  · simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, bSP, cSP] using bAligned
  · exact (copied.registers 19#5 (by decide)).trans
      (b19.trans (saveEntry_register s 0#5 (by decide)))
  · exact (copied.registers 20#5 (by decide)).trans
      (b20.trans (saveEntry_register s 4#5 (by decide)))
  · exact (copied.registers 21#5 (by decide)).trans
      (b21.trans (saveEntry_register s 3#5 (by decide)))
  · exact (copied.registers 22#5 (by decide)).trans
      (b22.trans (saveEntry_register s 2#5 (by decide)))
  · exact (copied.registers 23#5 (by decide)).trans
      (b23.trans (saveEntry_register s 1#5 (by decide)))
  · exact ((copied.registers 24#5 (by decide)).trans (b24.trans aSP)).trans cSP.symm
  · simpa only [cSP] using buffer
  · simpa only [cSP] using chaining

def metadataWrites (s : ArmState) : List Span :=
  [((r (.GPR 31#5) s).toNat - 16, 16), ((r (.GPR 31#5) s).toNat + 96, 16)]

theorem metadata_frame (s : ArmState) (low : 16 ≤ (r (.GPR 31#5) s).toNat)
    (physical : (r (.GPR 31#5) s).toNat + 112 ≤ 2^64) :
    MemoryFrame (metadataWrites s) s (metadata s) := by
  intro address outside
  have scratch := outside ((r (.GPR 31#5) s).toNat - 16, 16) (by simp [metadataWrites])
  have header := outside ((r (.GPR 31#5) s).toNat + 96, 16) (by simp [metadataWrites])
  rw [metadata_memory]
  simp only [metadataMemory]
  repeat' rw [BoolCodec.write_mem_bytes_frame _ _ 8 _ address (by bv_omega) (by bv_omega)]

theorem prelude_correct (s : ArmState) (base : BitVec 64) (left right : ByteArray)
    (code : CodeAt s base) (data : DataAt s base) (pc : read_pc s = base)
    (error : read_err s = .None) (aligned : CheckSPAlignment s)
    (owned : CombineOwned s base left right) :
    ∃ fuel, PreludePost s (run fuel s) base left right := by
  let firstFuel := 19 + (Memcpy.fuel 32 + 1)
  let t := run firstFuel s
  have ready : Initialized s t base := initialized_correct s base left right code data pc error aligned owned
  have low := owned.stackLow
  have spNat : (r (.GPR 31#5) t).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [ready.sp]; simp only [bodySP]; bv_omega
  have physical : (r (.GPR 31#5) t).toNat + 304 ≤ 2^64 := by
    have upper := (r (.GPR 31#5) s).isLt
    rw [spNat]; omega
  have localFrame := metadata_frame t (by rw [spNat]; omega) (by omega)
  have writes : ∀ span ∈ metadataWrites t, ∃ outer ∈ combineWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [metadataWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
        simp only [stackSpan, spNat] <;> omega
  have preserved (address bytes : Nat)
      (lo : (r (.GPR 31#5) t).toNat ≤ address)
      (hi : address + bytes ≤ (r (.GPR 31#5) t).toNat + 96) :
      Protected (metadataWrites t) address bytes := by
    right
    intro span member
    simp only [metadataWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> omega
  have buffer : BytesAt (metadata t) (r (.GPR 31#5) t)
      ⟨SszNative.HashStream.new.buffer.toArray⟩ :=
    bytesAt_frame localFrame (by rw [vectorByteArray_size]; omega)
      (by rw [vectorByteArray_size]; exact preserved _ _ (by omega) (by omega)) ready.buffer
  have chaining : ChainingAt (metadata t) (r (.GPR 31#5) t + 64#64) Ssz.Sha256.initialState :=
    ready.chaining.frame localFrame (by bv_omega)
      (preserved _ _ (by bv_omega) (by bv_omega))
  have saved : Saved s (metadata t) := ready.saved.of_frame localFrame physical
    (by
      right
      intro span member
      simp only [metadataWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [Prod.fst, Prod.snd] <;> bv_omega)
    (metadata_sp t)
    (by intro reg lo hi; exact metadata_register t reg (by bv_omega) (by bv_omega) (by bv_omega))
    (by intro reg lo hi; rw [metadata_vector])
  obtain ⟨buffered, byteLen⟩ := metadata_fields t (by rw [spNat]; omega) (by omega)
  have count : (r (.GPR 22#5) t).toNat = left.size := by rw [ready.x22]; exact owned.leftLength
  have represented : StateAt (metadata t) (r (.GPR 31#5) (metadata t))
      { SszNative.HashStream.new with byteLen := UInt64.ofNat left.size } := by
    rw [metadata_sp]
    refine ⟨buffer, chaining, ?_, ?_⟩
    · exact buffered
    · rw [byteLen]
      change r (.GPR 22#5) t = BitVec.ofNat 64 left.size
      bv_omega
  refine ⟨firstFuel + 13, ?_⟩
  rw [run_plus, metadata_run t base (code.of_program_eq ready.program) ready.error ready.aligned ready.pc]
  refine ⟨?_, (metadata_error t).trans ready.error, (metadata_program t).trans ready.program,
    ?_, (metadata_sp t).trans ready.sp, ?_, ?_, ?_, ?_, ?_, ?_, saved,
    represented, ready.frame.trans (frame_mono localFrame writes)⟩
  · rw [metadata_pc t base ready.pc, count]
    by_cases enough : 64 ≤ left.size
    · rw [if_pos enough, if_neg (by omega : ¬left.size / 64 = 0)]
    · rw [if_neg enough, if_pos (by omega : left.size / 64 = 0)]
  · simpa only [CheckSPAlignment, read_gpr, BitVec.setWidth_eq, metadata_sp] using ready.aligned
  · exact (metadata_register t 19#5 (by decide) (by decide) (by decide)).trans ready.x19
  · exact (metadata_register t 20#5 (by decide) (by decide) (by decide)).trans ready.x20
  · exact (metadata_register t 21#5 (by decide) (by decide) (by decide)).trans ready.x21
  · exact (metadata_register t 22#5 (by decide) (by decide) (by decide)).trans ready.x22
  · exact (metadata_register t 23#5 (by decide) (by decide) (by decide)).trans ready.x23
  · exact ((metadata_register t 24#5 (by decide) (by decide) (by decide)).trans ready.x24).trans
      (metadata_sp t).symm

theorem PreludePost.directOwned {s t : ArmState} {base : BitVec 64} {left right : ByteArray}
    (post : PreludePost s t base left right) (owned : CombineOwned s base left right) :
    DirectOwned t base (r (.GPR 1#5) s) left Ssz.Sha256.initialState := by
  have low := owned.stackLow
  have spNat : (r (.GPR 31#5) t).toNat = (r (.GPR 31#5) s).toNat - 304 := by
    rw [post.sp]; simp only [bodySP]; bv_omega
  have inclusion : ∀ span ∈ directWrites t, ∃ outer ∈ combineWrites s,
      outer.1 ≤ span.1 ∧ span.1 + span.2 ≤ outer.1 + outer.2 := by
    intro span member
    simp only [directWrites, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals
      refine ⟨stackSpan s 496, by simp [combineWrites], ?_, ?_⟩ <;>
        simp only [stackSpan, post.x24, spNat] <;> bv_omega
  refine ⟨owned.leftBound, ?_, ?_, ?_,
    protected_writes_mono owned.leftOwned inclusion,
    protected_writes_mono owned.initialOwned inclusion,
    protected_writes_mono owned.roundsOwned inclusion,
    bytesAt_frame post.frame owned.leftBound owned.leftOwned owned.left, ?_⟩
  · rw [post.x24, post.sp]
    simp only [bodySP]
    bv_omega
  · rw [spNat]; omega
  · right
    intro span member
    simp only [List.mem_singleton] at member
    subst span
    simp only [stackSpan, post.x24, spNat]
    bv_omega
  · simpa only [post.x24, SszNative.HashStream.new] using post.state.chaining

end SszArm.Hash.Combine
