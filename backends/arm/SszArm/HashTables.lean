import SszArm.HashMemory

namespace SszArm.Hash

theorem initialTable_size : initialTable.length = 32 := rfl

theorem roundsTable_size : roundsTable.length = 256 := by
  have size := roundsByteArray_size
  rw [← ByteArray.size_data] at size
  change roundsTable.toArray.size = 256 at size
  rwa [List.size_toArray] at size

/-- The actual linked little-endian IV table is the pinned semantic initializer. -/
theorem initialTable_byte (i : Fin 8) (lane : Fin 4) :
    (initialTable[4 * i.val + lane.val]'(by
      rw [initialTable_size]
      have hi := i.isLt
      have hl := lane.isLt
      omega)).toBitVec = (Ssz.Sha256.initialState[i.val]).toBitVec.extractLsByte lane.val := by
  rcases i with ⟨i, hi⟩
  rcases lane with ⟨lane, hl⟩
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    match lane, hl with
    | 0, _ | 1, _ | 2, _ | 3, _ => decide +revert

theorem initial_chaining (s : ArmState) (address : BitVec 64)
    (table : TableAt s address initialTable) (physical : address.toNat + 32 ≤ 2^64) :
    ChainingAt s address Ssz.Sha256.initialState := by
  intro i
  have hi := i.isLt
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes]
  apply BitVec.eq_of_extractLsByte_eq
  intro lane
  by_cases hl : lane < 4
  · have wordBound : (address + BitVec.ofNat 64 (4 * i.val)).toNat + 4 ≤ 2^64 := by bv_omega
    rw [Memory.extractLsByte_read_bytes wordBound, if_pos hl]
    change s.mem (address + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 lane) = _
    have addrEq : address + BitVec.ofNat 64 (4 * i.val) + BitVec.ofNat 64 lane =
        address + BitVec.ofNat 64 (4 * i.val + lane) := by bv_omega
    rw [addrEq]
    have source := table ⟨4 * i.val + lane, by
      change 4 * i.val + lane < initialTable.toArray.size
      rw [List.size_toArray, initialTable_size]
      omega⟩
    have encoding := initialTable_byte i ⟨lane, hl⟩
    simp only [ByteArray.getElem_eq_getElem_data, List.getElem_toArray] at source
    exact source.trans encoding
  · rw [BitVec.extractLsByte_ge (by omega), BitVec.extractLsByte_ge (by omega)]

end SszArm.Hash
