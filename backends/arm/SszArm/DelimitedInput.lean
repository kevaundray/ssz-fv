import SszArm.DelimitedScan
import SszArm.DelimitedResults

namespace SszArm.Delimited

open UintCodec (widthLoad)

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem scan_bytes_of_words (s : ArmState) (pointer : BitVec 64) (bytes : List (BitVec 8))
    (words : ∀ i : Fin bytes.length,
      read_mem_bytes 1 (pointer + BitVec.ofNat 64 i.val) s = bytes[i]) :
    ScanBytes s pointer bytes := by
  induction bytes generalizing pointer with
  | nil => trivial
  | cons byte bytes ih =>
    refine ⟨?_, ih (pointer + 1#64) ?_⟩
    · simpa using words ⟨0, by simp⟩
    · intro i
      have word := words ⟨i.val + 1, by simpa using i.isLt⟩
      have order : pointer + BitVec.ofNat 64 (i.val + 1) =
          (pointer + 1#64) + BitVec.ofNat 64 i.val := by bv_omega
      simpa [order] using word

def scanData (data : Ssz.Bytes) : List (BitVec 8) := data.toList.map UInt8.toBitVec

theorem bytes_to_scan (s : ArmState) (pointer : BitVec 64) (data : Ssz.Bytes)
    (input : SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat data) :
    ScanBytes s pointer (scanData data) := by
  apply scan_bytes_of_words
  intro i
  have hi : i.val < data.size := by simpa [scanData] using i.isLt
  change read_mem_bytes 1 (pointer + BitVec.ofNat 64 i.val) s =
    (data.toList.map UInt8.toBitVec).get i
  rw [List.get_eq_getElem, List.getElem_map, Array.getElem_toList]
  have word := Option.some.inj (input i.val hi)
  apply BitVec.eq_of_toNat_eq
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat, scanData,
    Array.getElem?_eq_getElem hi] using word

theorem scan_data_all (data : Ssz.Bytes) :
    (scanData data).all (· == 0#8) = data.all (· == 0) := by
  have byte_eq : ∀ byte : UInt8, (byte.toBitVec == 0#8) = (byte == 0) := by
    intro byte
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq, UInt8.toBitVec_ofNat] using
      (UInt8.toBitVec_inj (a := byte) (b := 0))
  simp [scanData, List.all_map, byte_eq]

theorem bytes_extract (s : ArmState) (pointer : BitVec 64) (data : Ssz.Bytes) (keep : Nat)
    (input : SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat data) :
    SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat (data.extract 0 keep) := by
  intro i hi
  have index : i < data.size := by simpa using Array.getElem_extract_aux hi
  simpa [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem index] using input i index

/-- The prologue's last-byte address is physical even at lengths above isize. -/
theorem last_byte (s : ArmState) (pointer length : BitVec 64) (data : Ssz.Bytes)
    (size : length.toNat = data.size) (nonempty : 0 < data.size)
    (input : SszNative.ByteView.BytesAt (widthLoad s) pointer.toNat data) :
    read_mem_bytes 1 (pointer + (length - 1#64)) s = data[data.size - 1]!.toBitVec := by
  have hi : data.size - 1 < data.size := by omega
  have offset : length - 1#64 = BitVec.ofNat 64 (data.size - 1) := by bv_omega
  rw [offset, getElem!_pos data (data.size - 1) hi]
  apply BitVec.eq_of_toNat_eq
  have word := Option.some.inj (input (data.size - 1) hi)
  simpa [widthLoad, BitVec.ofNat_add, BitVec.ofNat_toNat,
    Array.getElem?_eq_getElem hi] using word

end SszArm.Delimited
