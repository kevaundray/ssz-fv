import SszArm.Proofs
import SszUInt64

/-!
# The upstream SSZ byte bridge

`memoryBytes` observes the actual caller-owned model memory byte by byte. It does
not replace the machine semantics: `memoryBytes_eq_uintBytes` proves that this
observation agrees with the pinned upstream `Ssz.uintBytes` for the word that
LNSym reads. `storeProgram_ssz` and `loadProgram_ssz` then connect the raw machine
execution to that upstream serialization function.

The general byte-observation lemma permits modular model addresses. The store
bridge and public store frame explicitly require a non-wrapping caller-owned
region; their read-after-write proof is kernel checked without native SAT axioms.
-/

namespace SszArm

/-- An observation of successive bytes in the model's actual data memory. -/
def memoryBytes : (n : Nat) → BitVec 64 → Memory → Ssz.Bytes
  | 0, _, _ => #[]
  | n + 1, addr, mem =>
      #[UInt8.ofNat (mem addr).toNat] ++ memoryBytes n (addr + 1#64) mem

/-- LNSym's little-endian memory read agrees with upstream SSZ, at every width. -/
theorem memoryBytes_eq_uintBytes (n : Nat) (addr : BitVec 64) (mem : Memory) :
    memoryBytes n addr mem = Ssz.uintBytes n (mem.read_bytes n addr).toNat := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    have hb : (mem.read addr).toNat < 256 := (mem.read addr).isLt
    have hv : (mem.read_bytes (n + 1) addr).toNat =
        (mem.read_bytes n (addr + 1#64)).toNat * 256 + (mem.read addr).toNat := by
      simp only [Memory.read_bytes, BitVec.toNat_cast, BitVec.toNat_append]
      rw [← Nat.shiftLeft_add_eq_or_of_lt (mem.read addr).isLt, Nat.shiftLeft_eq]
    have hlo : ((mem.read_bytes n (addr + 1#64)).toNat * 256 +
        (mem.read addr).toNat) % 256 = (mem.read addr).toNat := by omega
    have hhi : ((mem.read_bytes n (addr + 1#64)).toNat * 256 +
        (mem.read addr).toNat) / 256 = (mem.read_bytes n (addr + 1#64)).toNat := by omega
    rw [hv, Ssz.uintBytes, hlo, hhi]
    change #[UInt8.ofNat (mem.read addr).toNat] ++ memoryBytes n (addr + 1#64) mem = _
    rw [ih]

/-- The returned load value serializes to exactly the eight original input bytes. -/
theorem loadProgram_bytes (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base loadProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) :
    Ssz.uintBytes 8 (r (.GPR 0) (run 2 s)).toNat =
      memoryBytes 8 (r (.GPR 0) s) s.mem := by
  rw [(loadProgram_correct s base hcode hpc herr).1]
  rw [Memory.State.read_mem_bytes_eq_mem_read_bytes]
  exact (memoryBytes_eq_uintBytes 8 (r (.GPR 0) s) s.mem).symm

/-- The actual eight stored bytes are the upstream serialization of x1. -/
theorem storeProgram_ssz (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base storeProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None)
    (hspace : (r (.GPR 0) s).toNat + 8 ≤ 2 ^ 64) :
    memoryBytes 8 (r (.GPR 0) s) (run 2 s).mem =
      Ssz.uintBytes 8 (r (.GPR 1) s).toNat := by
  rw [memoryBytes_eq_uintBytes, ← Memory.State.read_mem_bytes_eq_mem_read_bytes]
  rw [storeProgram_run s base hcode hpc herr]
  simp only [read_mem_bytes_of_w]
  rw [read_write_bytes s 8 (r (.GPR 0) s) (r (.GPR 1) s) hspace]

/-- A bounded natural-number SSZ value in caller memory is returned exactly. -/
theorem loadProgram_ssz (s : ArmState) (base : BitVec 64) (value : Nat)
    (hcode : CodeAt s base loadProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) (hfit : value < 2 ^ 64)
    (hbytes : memoryBytes 8 (r (.GPR 0) s) s.mem = Ssz.uintBytes 8 value) :
    (r (.GPR 0) (run 2 s)).toNat = value := by
  have same := (loadProgram_bytes s base hcode hpc herr).trans hbytes
  have decoded := congrArg (fun bytes => Ssz.readUint bytes 0 8) same
  simpa only [Ssz.readUint_uintBytes 8 _ (r (.GPR 0) (run 2 s)).isLt,
    Ssz.readUint_uintBytes 8 value hfit] using decoded

/-- The upstream public serializer returns exactly the machine-written bytes. -/
theorem storeProgram_serialize (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base storeProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None)
    (hspace : (r (.GPR 0) s).toNat + 8 ≤ 2 ^ 64) :
    Ssz.serialize (.uint 8) (.uint (r (.GPR 1) s).toNat) =
      .ok (memoryBytes 8 (r (.GPR 0) s) (run 2 s).mem) := by
  rw [storeProgram_ssz s base hcode hpc herr hspace]
  exact SszNative.serialize_uint64 _

/-- The machine's returned value equals public SSZ decoding of its input bytes. -/
theorem loadProgram_deserialize (s : ArmState) (base : BitVec 64)
    (hcode : CodeAt s base loadProgram) (hpc : read_pc s = base)
    (herr : read_err s = .None) :
    Ssz.deserialize (.uint 8) (memoryBytes 8 (r (.GPR 0) s) s.mem) =
      .ok (.uint (r (.GPR 0) (run 2 s)).toNat) := by
  rw [← loadProgram_bytes s base hcode hpc herr]
  exact SszNative.deserialize_uint64 _

end SszArm
