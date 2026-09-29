import SszX86.HashFinalizeExec

namespace SszX86.Hash.Finalize
open WordNormalize

/-- These are precisely the byte permutations performed by the two BSWAP widths. -/
def swap32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++
    a.extractLsb' 16 8 ++ a.extractLsb' 24 8

def swap64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++
    a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++
    a.extractLsb' 48 8 ++ a.extractLsb' 56 8

theorem load_length_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (value : BitVec 64) (P : MachineState → Prop)
    (readValue : Mem.loadInt s.dmem (get s .r14 + 104) 8 = some (value.toNat : Int))
    (next : Eventually (step e) P (put s .rax value, base + 120)) :
    Eventually (step e) P (s, base + 116) := by
  hash_finalize_step 31 using hc
  simp only [MachineData.load, Width.bytes, Width.bits, Effects.All, get, UintCodec.Large.get,
    Reg64s.get64, WordNormalize.bitvecNumeral] at readValue ⊢
  rw [readValue]
  word_simpa [put, UintCodec.Large.put, Reg64s.set64,
    Effects.All, Width.bits, BitVec.ofInt_natCast] using next

private theorem int64_numeral (n : Nat) :
    (OfNat.ofNat n : Int64) = Int64.ofNat n := rfl

private theorem shift_three_word (a : UInt64) :
    a <<< UInt64.ofBitVec (BitVec.ofNat 64 3) =
      UInt64.ofBitVec (a.toBitVec <<< (3 : Nat)) := by
  word_simpa [] using (UInt64.ofBitVec_shiftLeft a.toBitVec 3 (by decide)).symm

/-- SHL is modular on all UInt64 counts. No logical message-length cap occurs. -/
theorem shift_length_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P
      (putF s .rax (get s .rax <<< (3 : Nat)) flags, base + 124)) :
    Eventually (step e) P (s, base + 120) := by
  have shiftCount : (BitVec.extractLsb' 0 8 (Int64.toBitVec 3)).toNat &&& 63 = 3 := by decide
  hash_finalize_step 32 using hc
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
    BitVec.take, shiftCount]
  simp [Effects.All]
  repeat' first | apply And.intro | intro
  all_goals word_simpa [putF, put, get, UintCodec.Large.putF,
    UintCodec.Large.put, UintCodec.Large.get, Reg64s.set64, Reg64s.get64,
    Effects.All, shift_three_word] using next _

theorem swap_length_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P (put s .rax (swap64 (get s .rax)), base + 127)) :
    Eventually (step e) P (s, base + 124) := by
  hash_finalize_step 33 using hc
  word_simpa [swap64, put, get, UintCodec.Large.put, UintCodec.Large.get,
    Reg64s.set64, Reg64s.get64, BitVec.take, BitVec.drop, Effects.All,
    BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)] using next

def lengthState (s : MachineData) : MachineData :=
  { s with dmem := Mem.storeInt s.dmem (get s .r14 + 56) 8 (get s .rax).toInt }

theorem store_length_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (mapping : ∃ old, Mem.loadInt s.dmem (get s .r14 + 56) 8 = some old)
    (next : Eventually (step e) P (lengthState s, base + 131)) :
    Eventually (step e) P (s, base + 127) := by
  hash_finalize_step 34 using hc
  apply Delimited.store_cps
  · word_simpa [get, UintCodec.Large.get, Reg64s.get64, Width.bytes] using mapping
  word_simpa [lengthState, get, UintCodec.Large.get, Reg64s.get64,
    Effects.All, Width.bytes] using next

inductive DigestWord where
  | a | b | c | d | e | f | g | h

def DigestWord.reg : DigestWord → Reg64
  | .a => .rax | .b => .rcx | .c => .rdx | .d => .rsi
  | .e => .rdi | .f => .r8 | .g => .r9 | .h => .r10

def DigestWord.offset : DigestWord → Nat
  | .a => 0 | .b => 4 | .c => 8 | .d => 12
  | .e => 16 | .f => 20 | .g => 24 | .h => 28

def DigestWord.loadPc : DigestWord → Nat
  | .a => 143 | .b => 147 | .c => 155 | .d => 161
  | .e => 167 | .f => 173 | .g => 180 | .h => 187

def DigestWord.loadNext : DigestWord → Nat
  | .a => 147 | .b => 151 | .c => 159 | .d => 165
  | .e => 171 | .f => 177 | .g => 184 | .h => 191

def DigestWord.swapPc : DigestWord → Nat
  | .a => 151 | .b => 153 | .c => 159 | .d => 165
  | .e => 171 | .f => 177 | .g => 184 | .h => 191

def DigestWord.swapNext : DigestWord → Nat
  | .a => 153 | .b => 155 | .c => 161 | .d => 167
  | .e => 173 | .f => 180 | .g => 187 | .h => 194

def DigestWord.storePc : DigestWord → Nat
  | .a => 194 | .b => 196 | .c => 199 | .d => 202
  | .e => 205 | .f => 208 | .g => 212 | .h => 216

def DigestWord.storeNext : DigestWord → Nat
  | .a => 196 | .b => 199 | .c => 202 | .d => 205
  | .e => 208 | .f => 212 | .g => 216 | .h => 220

macro "finalize_digest_load_finish " readValue:ident ", " next:ident : tactic => `(tactic|
  (simp only [DigestWord.offset, get, UintCodec.Large.get, Reg64s.get64,
      MachineData.load, Width.bytes, Width.bits, Effects.All, WordNormalize.bitvecNumeral] at $readValue:ident ⊢
   rw [($readValue:ident)]
   word_simpa [DigestWord.reg, DigestWord.loadNext, put, UintCodec.Large.put,
     Reg64s.set64, Effects.All, Width.bits, BitVec.ofInt_natCast, int64_numeral,
     BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)] using $next))

/-- Each chaining word is read by its actual four-byte MOV, not a wide load. -/
theorem digest_load_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (which : DigestWord) (s : MachineData) (value : BitVec 32) (P : MachineState → Prop)
    (readValue : Mem.loadInt s.dmem (get s .r14 + BitVec.ofNat 64 (64 + which.offset)) 4 =
      some (value.toNat : Int))
    (next : Eventually (step e) P
      (put s which.reg (value.setWidth 64), base + Int64.ofNat which.loadNext)) :
    Eventually (step e) P (s, base + Int64.ofNat which.loadPc) := by
  cases which
  · hash_finalize_step 38 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 39 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 42 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 44 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 46 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 48 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 50 using hc
    finalize_digest_load_finish readValue, next
  · hash_finalize_step 52 using hc
    finalize_digest_load_finish readValue, next

macro "finalize_digest_swap_finish " next:ident : tactic => `(tactic|
  (word_simpa [DigestWord.reg, DigestWord.swapNext, swap32,
    put, get, UintCodec.Large.put, UintCodec.Large.get, Reg64s.set64, Reg64s.get64,
    BitVec.take, BitVec.drop, Effects.All, int64_numeral,
    BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)] using $next))

theorem digest_swap_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (which : DigestWord) (s : MachineData) (P : MachineState → Prop)
    (next : Eventually (step e) P
      (put s which.reg ((swap32 ((get s which.reg).setWidth 32)).setWidth 64),
        base + Int64.ofNat which.swapNext)) :
    Eventually (step e) P (s, base + Int64.ofNat which.swapPc) := by
  cases which
  · hash_finalize_step 40 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 41 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 43 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 45 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 47 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 49 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 51 using hc
    finalize_digest_swap_finish next
  · hash_finalize_step 53 using hc
    finalize_digest_swap_finish next

def digestStoreState (which : DigestWord) (s : MachineData) : MachineData :=
  { s with
    dmem := Mem.storeInt s.dmem (get s .rbx + BitVec.ofNat 64 which.offset) 4
      ((get s which.reg).setWidth 32).toInt }

macro "finalize_digest_store_finish " mapping:ident ", " next:ident : tactic => `(tactic|
  (apply Delimited.store_cps
   · word_simpa [DigestWord.offset, get, UintCodec.Large.get, Reg64s.get64,
       BitVec.add_zero, Width.bytes] using $mapping
   word_simpa [digestStoreState, DigestWord.offset, DigestWord.reg,
     DigestWord.storeNext, get, UintCodec.Large.get, Reg64s.get64,
     BitVec.take, Effects.All, Width.bytes, Width.bits, int64_numeral,
     BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)] using $next))

theorem digest_store_runs (e : Executable) (base : Int64) (hc : CodeAt e base)
    (which : DigestWord) (s : MachineData) (P : MachineState → Prop)
    (mapping : ∃ old, Mem.loadInt s.dmem
      (get s .rbx + BitVec.ofNat 64 which.offset) 4 = some old)
    (next : Eventually (step e) P
      (digestStoreState which s, base + Int64.ofNat which.storeNext)) :
    Eventually (step e) P (s, base + Int64.ofNat which.storePc) := by
  cases which
  · hash_finalize_step 54 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 55 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 56 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 57 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 58 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 59 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 60 using hc
    finalize_digest_store_finish mapping, next
  · hash_finalize_step 61 using hc
    finalize_digest_store_finish mapping, next

end SszX86.Hash.Finalize
