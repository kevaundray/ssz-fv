import SszX86.HashFinalizeLength

namespace SszX86.Hash.Finalize
open SszNative.HashStream WordNormalize

private theorem widen_low32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  bv_omega

def digestLoaded (s : MachineData) (words : Vector UInt32 8) : MachineData :=
  { s with regs := { s.regs with
    rax := UInt64.ofBitVec ((swap32 words[0].toBitVec).setWidth 64)
    rcx := UInt64.ofBitVec ((swap32 words[1].toBitVec).setWidth 64)
    rdx := UInt64.ofBitVec ((swap32 words[2].toBitVec).setWidth 64)
    rsi := UInt64.ofBitVec ((swap32 words[3].toBitVec).setWidth 64)
    rdi := UInt64.ofBitVec ((swap32 words[4].toBitVec).setWidth 64)
    r8 := UInt64.ofBitVec ((swap32 words[5].toBitVec).setWidth 64)
    r9 := UInt64.ofBitVec ((swap32 words[6].toBitVec).setWidth 64)
    r10 := UInt64.ofBitVec ((swap32 words[7].toBitVec).setWidth 64) } }

macro "finalize_word_load " which:term " wordValue " v:term " using " hc:term ", " readValue:term : tactic => `(tactic|
  (apply digest_load_runs _ _ $hc $which _ $v
   · simpa only [DigestWord.offset, put, get, UintCodec.Large.put,
       UintCodec.Large.get, Reg64s.set64, Reg64s.get64,
       UInt64.toBitVec_ofBitVec] using $readValue))

/-- The eight scalar reads and eight BSWAPs precede every output store. -/
theorem digest_read_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (s : MachineData) (words : Vector UInt32 8)
    (chain : ChainingAt s.dmem (s.regs.r14.toBitVec + 64) words)
    (P : MachineState → Prop)
    (next : Eventually (step e) P (digestLoaded s words, root - 256 + 194)) :
    Eventually (step e) P (s, root - 256 + 143) := by
  have readWord (i : Nat) (hi : i < 8) :
      Mem.loadInt s.dmem (s.regs.r14.toBitVec + BitVec.ofNat 64 (64 + 4 * i)) 4 =
        some (words[i].toBitVec.toNat : Int) := by
    have h := chainingAt_load _ _ _ chain i hi
    rw [scalar_bytes_value 4 words[i].toNat (by exact words[i].toBitVec.isLt)] at h
    simpa only [memmove_addr_add] using h
  finalize_word_load DigestWord.a wordValue words[0].toBitVec using hc.finalize, readWord 0 (by decide)
  finalize_word_load DigestWord.b wordValue words[1].toBitVec using hc.finalize, readWord 1 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .a
  apply digest_swap_runs e (root - 256) hc.finalize .b
  finalize_word_load DigestWord.c wordValue words[2].toBitVec using hc.finalize, readWord 2 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .c
  finalize_word_load DigestWord.d wordValue words[3].toBitVec using hc.finalize, readWord 3 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .d
  finalize_word_load DigestWord.e wordValue words[4].toBitVec using hc.finalize, readWord 4 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .e
  finalize_word_load DigestWord.f wordValue words[5].toBitVec using hc.finalize, readWord 5 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .f
  finalize_word_load DigestWord.g wordValue words[6].toBitVec using hc.finalize, readWord 6 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .g
  finalize_word_load DigestWord.h wordValue words[7].toBitVec using hc.finalize, readWord 7 (by decide)
  apply digest_swap_runs e (root - 256) hc.finalize .h
  word_simpa [digestLoaded, DigestWord.reg, DigestWord.swapNext, put, get,
    UintCodec.Large.put, UintCodec.Large.get, Reg64s.set64, Reg64s.get64,
    widen_low32] using next

def digestMem (m : DataMem) (out : BitVec 64) (words : Vector UInt32 8) : DataMem :=
  Mem.storeInt (Mem.storeInt (Mem.storeInt (Mem.storeInt
    (Mem.storeInt (Mem.storeInt (Mem.storeInt (Mem.storeInt m
      out 4 (swap32 words[0].toBitVec).toInt)
      (out + 4) 4 (swap32 words[1].toBitVec).toInt)
      (out + 8) 4 (swap32 words[2].toBitVec).toInt)
      (out + 12) 4 (swap32 words[3].toBitVec).toInt)
      (out + 16) 4 (swap32 words[4].toBitVec).toInt)
      (out + 20) 4 (swap32 words[5].toBitVec).toInt)
      (out + 24) 4 (swap32 words[6].toBitVec).toInt)
      (out + 28) 4 (swap32 words[7].toBitVec).toInt

def digestWritten (s : MachineData) (words : Vector UInt32 8) : MachineData :=
  { digestLoaded s words with dmem := digestMem s.dmem s.regs.rbx.toBitVec words }

macro "finalize_word_store " which:term " byteOffset " off:num " using " hc:term ", " mapping:term : tactic => `(tactic|
  (apply digest_store_runs _ _ $hc $which
   · apply UintCodec.Large.mapped_load _ _ 32 $off 4
     · repeat' first | exact $mapping | apply UintCodec.Large.mapped_store
     · decide))

theorem digest_write_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (s : MachineData) (words : Vector UInt32 8)
    (mapping : Mapped s.dmem s.regs.rbx.toBitVec 32) (P : MachineState → Prop)
    (next : Eventually (step e) P (digestWritten s words, root - 256 + 220)) :
    Eventually (step e) P (digestLoaded s words, root - 256 + 194) := by
  finalize_word_store DigestWord.a byteOffset 0 using hc.finalize, mapping
  finalize_word_store DigestWord.b byteOffset 4 using hc.finalize, mapping
  finalize_word_store DigestWord.c byteOffset 8 using hc.finalize, mapping
  finalize_word_store DigestWord.d byteOffset 12 using hc.finalize, mapping
  finalize_word_store DigestWord.e byteOffset 16 using hc.finalize, mapping
  finalize_word_store DigestWord.f byteOffset 20 using hc.finalize, mapping
  finalize_word_store DigestWord.g byteOffset 24 using hc.finalize, mapping
  finalize_word_store DigestWord.h byteOffset 28 using hc.finalize, mapping
  word_simpa [digestWritten, digestLoaded, digestMem, digestStoreState,
    DigestWord.reg, DigestWord.offset, DigestWord.storeNext, get, UintCodec.Large.get,
    Reg64s.get64, widen_low32] using next

private theorem other_word (m : DataMem) (out : BitVec 64) (write read lane : Nat)
    (writeBound : write < 8) (readBound : read < 8) (laneBound : lane < 4)
    (different : write ≠ read) (value : Int) :
    (Mem.storeInt m (out + BitVec.ofNat 64 (4 * write)) 4 value).get?
      (out + BitVec.ofNat 64 (4 * read + lane)) =
      m.get? (out + BitVec.ofNat 64 (4 * read + lane)) := by
  apply memmove_store_lookup_outside
  intro j hj equal
  have hj' : j < 4 := by simpa only [Int.toBytes_length] using hj
  bv_omega

private theorem same_word (m : DataMem) (out : BitVec 64) (wordIndex lane : Nat)
    (laneBound : lane < 4) (value : Int) :
    (Mem.storeInt m (out + BitVec.ofNat 64 (4 * wordIndex)) 4 value).get?
      (out + BitVec.ofNat 64 (4 * wordIndex + lane)) = (Int.toBytes 4 value)[lane]? := by
  rw [← memmove_addr_add]
  exact memmove_store_lookup_inside m _ _ lane (by simpa using laneBound) (by simp)

theorem digestMem_word (m : DataMem) (out : BitVec 64) (words : Vector UInt32 8)
    (wordIndex : Fin 8) (lane : Fin 4) :
    (digestMem m out words).get? (out + BitVec.ofNat 64 (4 * wordIndex.val + lane.val)) =
      (Int.toBytes 4 (swap32 words[wordIndex.val].toBitVec).toInt)[lane.val]? := by
  rcases wordIndex with ⟨wordIndex, bound⟩
  have outside (m : DataMem) (write read : Nat) (hw : write < 8) (hr : read < 8)
      (different : write ≠ read) (v : Int) :=
    other_word m out write read lane.val hw hr lane.isLt different v
  have inside (m : DataMem) (wordIndex : Nat) (v : Int) := same_word m out wordIndex lane.val lane.isLt v
  match wordIndex, bound with
  | 0, _ =>
    unfold digestMem
    rw [outside _ 7 0 (by decide) (by decide) (by decide),
      outside _ 6 0 (by decide) (by decide) (by decide),
      outside _ 5 0 (by decide) (by decide) (by decide),
      outside _ 4 0 (by decide) (by decide) (by decide),
      outside _ 3 0 (by decide) (by decide) (by decide),
      outside _ 2 0 (by decide) (by decide) (by decide),
      outside _ 1 0 (by decide) (by decide) (by decide)]
    simpa only [BitVec.add_zero] using inside _ 0 _
  | 1, _ =>
    unfold digestMem
    rw [outside _ 7 1 (by decide) (by decide) (by decide),
      outside _ 6 1 (by decide) (by decide) (by decide),
      outside _ 5 1 (by decide) (by decide) (by decide),
      outside _ 4 1 (by decide) (by decide) (by decide),
      outside _ 3 1 (by decide) (by decide) (by decide),
      outside _ 2 1 (by decide) (by decide) (by decide)]
    exact inside _ 1 _
  | 2, _ =>
    unfold digestMem
    rw [outside _ 7 2 (by decide) (by decide) (by decide),
      outside _ 6 2 (by decide) (by decide) (by decide),
      outside _ 5 2 (by decide) (by decide) (by decide),
      outside _ 4 2 (by decide) (by decide) (by decide),
      outside _ 3 2 (by decide) (by decide) (by decide)]
    exact inside _ 2 _
  | 3, _ =>
    unfold digestMem
    rw [outside _ 7 3 (by decide) (by decide) (by decide),
      outside _ 6 3 (by decide) (by decide) (by decide),
      outside _ 5 3 (by decide) (by decide) (by decide),
      outside _ 4 3 (by decide) (by decide) (by decide)]
    exact inside _ 3 _
  | 4, _ =>
    unfold digestMem
    rw [outside _ 7 4 (by decide) (by decide) (by decide),
      outside _ 6 4 (by decide) (by decide) (by decide),
      outside _ 5 4 (by decide) (by decide) (by decide)]
    exact inside _ 4 _
  | 5, _ =>
    unfold digestMem
    rw [outside _ 7 5 (by decide) (by decide) (by decide),
      outside _ 6 5 (by decide) (by decide) (by decide)]
    exact inside _ 5 _
  | 6, _ =>
    unfold digestMem
    rw [outside _ 7 6 (by decide) (by decide) (by decide)]
    exact inside _ 6 _
  | 7, _ =>
    unfold digestMem
    exact inside _ 7 _
  | wordIndex + 8, bound => omega

theorem digestMem_bytes (m : DataMem) (out : BitVec 64) (words : Vector UInt32 8) :
    BytesAt (digestMem m out words) out (Ssz.Sha256.digest words).data.toList := by
  intro i hi
  have bound : i < 32 := by simpa [Ssz.Sha256.digest] using hi
  let wordIndex : Fin 8 := ⟨i / 4, by omega⟩
  let lane : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by decide)⟩
  have index : 4 * wordIndex.val + lane.val = i := by dsimp [wordIndex, lane]; omega
  have h := (digestMem_word m out words wordIndex lane).trans (digest_store_byte words wordIndex lane)
  simpa only [index] using h

theorem digestMem_frame (m : DataMem) (out : BitVec 64) (words : Vector UInt32 8) :
    MemoryFrame m (digestMem m out words) (fun a => InSpan a out 32) := by
  intro a outside
  have unchanged (m : DataMem) (offset : Nat) (bound : offset + 4 ≤ 32) (value : Int) :
      (Mem.storeInt m (out + BitVec.ofNat 64 offset) 4 value).get? a = m.get? a := by
    apply memmove_store_lookup_outside
    intro j hj equal
    have hj' : j < 4 := by simpa using hj
    apply outside
    refine ⟨offset + j, by omega, ?_⟩
    simpa only [memmove_addr_add] using equal
  unfold digestMem
  rw [unchanged _ 28 (by decide), unchanged _ 24 (by decide), unchanged _ 20 (by decide),
    unchanged _ 16 (by decide), unchanged _ 12 (by decide), unchanged _ 8 (by decide),
    unchanged _ 4 (by decide)]
  simpa only [BitVec.add_zero] using unchanged _ 0 (by decide) _

/-- Exact 32-byte digest, original RET, SysV registers, frame and stack ownership. -/
theorem digest_return_runs (e : Executable) (root : Int64) (hc : LinkedCode e root)
    (entry : MachineData) (state : Model) (ra : BitVec 64)
    (pre : FinalizePre root entry state ra)
    (s : MachineData) (buf : Vector UInt8 64) (chain : Vector UInt32 8)
    (live : BufferPost root entry state ra buf chain s)
    (digest : Ssz.Sha256.digest chain = finalize state) :
    Eventually (step e) (FinalizePost entry state ra) (s, root - 256 + 143) := by
  apply digest_read_runs e root hc s chain
  · simpa only [live.regs.state] using live.chaining
  apply digest_write_runs e root hc s chain
  · simpa only [live.regs.output] using live.memory.output
  let result := digestWritten s chain
  have frame : MemoryFrame s.dmem result.dmem (WorkWritable entry) := by
    apply frame_mono _ _ _ _ (digestMem_frame s.dmem s.regs.rbx.toBitVec chain)
    intro a inside
    exact Or.inl (by simpa only [live.regs.output] using inside)
  have maps : MappedPreserved s.dmem result.dmem := by
    intro p n hm
    change Mapped (digestMem s.dmem s.regs.rbx.toBitVec chain) p n
    unfold digestMem
    repeat' first | exact hm | apply UintCodec.Large.mapped_store
  have memory := memory_update root entry state ra pre s.dmem result.dmem live.memory frame maps
  have regs : RegsLive entry result := live.regs
  apply return_runs e (root - 256) hc.finalize result entry.regs.rbx.toBitVec entry.regs.r14.toBitVec ra
  · simpa only [regs.stack] using memory.saved
  intro flags
  refine ⟨returnState_returned entry result ra flags regs.stack regs.rbp regs.r12 regs.r13 regs.r15,
    ?_, memory.frame, memory.stack⟩
  change BytesAt result.dmem entry.regs.rdi.toBitVec (finalize state).data.toList
  rw [← digest]
  simpa only [result, digestWritten, live.regs.output] using
    digestMem_bytes s.dmem s.regs.rbx.toBitVec chain

end SszX86.Hash.Finalize
