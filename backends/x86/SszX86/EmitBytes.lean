import SszX86.EmitBytesMemory

namespace SszX86.Emit.Bytes
open BoolCodec UintCodec

/-- Both byte-vector and byte-list native paths use the actual linked memcpy.
The source, result and stack ownership all come from the incoming body state. -/
theorem body_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (bytes : Ssz.Bytes) (src : BitVec 64) (owned : Owned s bytes src) :
    Eventually (step e) (fun t => t.2 = base + 1593 ∧ BodyPost s bytes t.1)
      (s, base + 256) := by
  have countNat : (UInt64.ofNat bytes.size).toNat = bytes.size := by
    change (BitVec.ofNat 64 bytes.size).toNat = bytes.size
    exact Nat.mod_eq_of_lt owned.bound
  apply type_guard e base hc s _ owned.tag
  apply length_load e base hc (tagged s) bytes.size _ owned.length
  apply capacity_guard e base hc
  · simpa only [lengthLoaded, tagged, countNat] using owned.capacity
  apply copy_prepare e base hc (compared (lengthLoaded (tagged s) bytes.size)) src _ owned.pointer
  have source : ListBytesAt (ready s bytes src).dmem (ready s bytes src).regs.rsi.toBitVec
      bytes.toList := by
    intro i hi
    have within : i < bytes.size := by simpa only [Array.length_toList] using hi
    simpa only [ready, copyReady, compared, lengthLoaded, tagged, UInt64.toBitVec_ofBitVec,
      List.getElem?_eq_getElem hi, Array.getElem_toList] using owned.source i within
  have run := copy_call_runs e base hc helper .bytes (ready s bytes src) bytes.toList
    (by simp only [ready, copyReady, compared, lengthLoaded, tagged,
      UInt64.toBitVec_ofNat', Array.length_toList])
    (by simpa only [Array.length_toList] using owned.bound) source
    (by simpa only [ready, copyReady, compared, lengthLoaded, tagged, Array.length_toList]
      using owned.output)
    owned.stack
    (by simpa only [ready, copyReady, compared, lengthLoaded, tagged,
      UInt64.toBitVec_ofBitVec, Array.length_toList] using owned.sourceOutput)
    (by simpa only [ready, copyReady, compared, lengthLoaded, tagged,
      UInt64.toBitVec_ofBitVec, Array.length_toList] using owned.sourceStack)
    (by simpa only [ready, copyReady, compared, lengthLoaded, tagged, Array.length_toList]
      using owned.outputStack)
  apply eventually_trans (step e) _ _ _ run
  rintro ⟨t, pc⟩ post
  have target := post.returned.1
  change pc = Int64.ofBitVec (base + 299).toBitVec at target
  rw [Int64.ofBitVec_toBitVec] at target
  subst pc
  apply finish e base hc t _ (copied_result_mapped s bytes src _ owned _ post)
  apply Eventually.done
  exact ⟨rfl, copied_post s bytes src _ owned _ post⟩

end SszX86.Emit.Bytes
