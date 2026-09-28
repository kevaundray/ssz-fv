import SszX86.SerializeDecode

namespace SszX86.Serialize
open SszNative SszNative.Limbs UintCodec
open Kraken.X64.Parser

private theorem host_member0 (index : Nat) (within : index < programChunk0.length) :
    programChunk0[index] ∈ program :=
  List.mem_append_left _ (List.getElem_mem within)

private theorem host_member1 (index : Nat) (within : index < programChunk1.length) :
    programChunk1[index] ∈ program :=
  List.mem_append_right _ (List.getElem_mem within)

/-- Match one concrete instruction against its bounded chunk membership. The
full wrapper is never unfolded by the instruction simplifier. -/
macro "host_checked_step " member:term " at " pc:num " encodedWidth " bytes:num
    " opcodeAST " instructions:term " using " hc:term : tactic => `(tactic|
  (apply step_cps
   have fetched := SszX86.Serialize.step_at _ _ $hc
     (($pc, $bytes, $instructions) : Nat × Nat × Program) $member
   apply (fetched _ _).mpr
   simp (config := {instances := true})
     [SszX86.Serialize.directives, SszX86.Serialize.labels,
      Directives.interp, Directive.interp, Instr.interp, Operation.interp,
      Operand.interp, RegOrMem.interp, Reg.interp, AddrExpr.interp, ConstExpr.interp,
      RelRegOrMem.interp, BitVec.toAddressSize, MachineData.set, MachineData.setReg,
      Reg64s.set, Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
      BitVec.drop, BitVec.take, BitVec.signed, BitVec.zero, BitVec.replaceLow,
      BitVec.extractLsb'_append_eq_right, Effects.All, CondCode.interp,
      BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
      Int64.add_assoc, Width.bytesv]))

/-- The host-size conversion only reads memory. RCX/RDX are countdown scratch;
R9 becomes the host size. In particular the pointer, stack, output, capacity,
and all saved argument registers retain their original values. -/
structure HostFrame (s t : MachineData) : Prop where
  memory : t.dmem = s.dmem
  vectors : t.zmms = s.zmms
  registers : ∀ r, r ≠ .rcx → r ≠ .rdx → r ≠ .r9 →
    t.regs.get64 r = s.regs.get64 r

theorem HostFrame.trans {s t u : MachineData} (first : HostFrame s t)
    (second : HostFrame t u) : HostFrame s u := by
  refine ⟨second.memory.trans first.memory, second.vectors.trans first.vectors, ?_⟩
  intro r hc hd h9
  exact (second.registers r hc hd h9).trans (first.registers r hc hd h9)

theorem host_status_frame (s : MachineData) (flags : StatusFlags) :
    HostFrame s {s with status := flags} := ⟨rfl, rfl, by intros; rfl⟩

/-- The stored physical length in R9 is deliberately not normalized here. -/
def hostScanState (s : MachineData) (index previous : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with
    regs := {s.regs with
      rcx := UInt64.ofBitVec index
      rdx := UInt64.ofBitVec previous}
    status := flags}

def hostValueState (s : MachineData) (limb : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  {s with regs := {s.regs with r9 := UInt64.ofBitVec limb}, status := flags}

theorem host_scan_frame (s : MachineData) (index previous : BitVec 64)
    (flags : StatusFlags) : HostFrame s (hostScanState s index previous flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r hc hd h9
  cases r <;> simp_all [hostScanState, Reg64s.get64]

theorem host_value_frame (s : MachineData) (limb : BitVec 64)
    (flags : StatusFlags) : HostFrame s (hostValueState s limb flags) := by
  refine ⟨rfl, rfl, ?_⟩
  intro r hc hd h9
  cases r <;> simp_all [hostValueState, Reg64s.get64]

/-- PC208--227 reads the actual last remaining stored limb before decrementing
both scratch registers. The conditional branch retains the comparison flags. -/
theorem host_scan_step (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (old limb : BitVec 64) (flags : StatusFlags)
    (n : Nat) (bound : n + 2 < 2 ^ 64)
    (stored : Mem.loadInt s.dmem
      (s.regs.rax.toBitVec + BitVec.ofNat 64 (8 * n)) 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (zero : limb = 0#64 → ∀ flags, Eventually (step e) P
      (hostScanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags,
        base + 208))
    (nonzero : limb ≠ 0#64 → ∀ flags, Eventually (step e) P
      (hostScanState s (BitVec.ofNat 64 (n + 1)) (BitVec.ofNat 64 (n + 1)) flags,
        base + 229)) :
    Eventually (step e) P
      (hostScanState s (BitVec.ofNat 64 (n + 2)) old flags, base + 208) := by
  have target := hc.targets ("serialize_u208", 208) (by decide)
  have different : BitVec.ofNat 64 (n + 2) ≠ 1#64 := by bv_omega
  have decrement : BitVec.ofNat 64 (n + 2) + 18446744073709551615#64 =
      BitVec.ofNat 64 (n + 1) := by bv_omega
  have decrementReg : (OfNat.ofNat (n + 2) : UInt64) + OfNat.ofNat 18446744073709551615 =
      OfNat.ofNat (n + 1) := by
    apply UInt64.toBitVec_inj.1
    change BitVec.ofNat 64 (n + 2) + 18446744073709551615#64 =
      BitVec.ofNat 64 (n + 1)
    exact decrement
  have address : s.regs.rax.toBitVec + BitVec.ofNat 64 (n + 2) * 8#64 +
      18446744073709551600#64 =
      s.regs.rax.toBitVec + BitVec.ofNat 64 (8 * n) := by bv_omega
  simp only [hostScanState]
  host_checked_step (host_member0 53 (by decide)) at 208 encodedWidth 4
    opcodeAST parse("cmpq $0x1,%rcx") using hc
  host_checked_step (host_member0 54 (by decide)) at 212 encodedWidth 2
    opcodeAST parse("je serialize_u300") using hc
  simp [StatusFlags.from_result, different, Effects.All]
  host_checked_step (host_member0 55 (by decide)) at 214 encodedWidth 4
    opcodeAST parse("leaq -0x1(%rcx),%rdx") using hc
  host_checked_step (host_member0 56 (by decide)) at 218 encodedWidth 6
    opcodeAST parse("cmpq $0x0,-0x10(%rax,%rcx,8)") using hc
  simp only [MachineData.load, Width.bytes, Effects.All]
  rw [address, stored]
  simp only [Effects.All, Width.bits, Delimited.word_cast]
  host_checked_step (host_member0 57 (by decide)) at 224 encodedWidth 3
    opcodeAST parse("movq %rdx,%rcx") using hc
  host_checked_step (host_member0 58 (by decide)) at 227 encodedWidth 2
    opcodeAST parse("je serialize_u208") using hc
  rw [decrementReg]
  by_cases isZero : limb = 0#64
  · simpa [isZero, target, hostScanState, StatusFlags.from_result, Effects.All] using
      zero isZero _
  · simpa [isZero, hostScanState, StatusFlags.from_result, Effects.All] using
      nonzero isZero _

/-- Induction follows physical storage, not logical limb count. Empty slices and
arbitrarily padded all-zero slices reach PC300 without an out-of-bounds read. -/
theorem host_scan_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (words : List (BitVec 64))
    (bound : words.length + 1 < 2 ^ 64)
    (stored : ∀ i : Fin words.length, Mem.loadInt s.dmem
      (s.regs.rax.toBitVec + BitVec.ofNat 64 (8 * i.val)) 8 = some (words[i].toNat : Int))
    (P : MachineState → Prop) :
    ∀ n, n ≤ words.length → ∀ old flags,
    (significantCount words n = 0 → ∀ old flags, Eventually (step e) P
      (hostScanState s 1 old flags, base + 300)) →
    (0 < significantCount words n → ∀ flags, Eventually (step e) P
      (hostScanState s (BitVec.ofNat 64 (significantCount words n))
        (BitVec.ofNat 64 (significantCount words n)) flags, base + 229)) →
    Eventually (step e) P
      (hostScanState s (BitVec.ofNat 64 (n + 1)) old flags, base + 208) := by
  intro n
  induction n with
  | zero =>
    intro within old flags empty nonempty
    have target := hc.targets ("serialize_u300", 300) (by decide)
    simp only [hostScanState]
    host_checked_step (host_member0 53 (by decide)) at 208 encodedWidth 4
      opcodeAST parse("cmpq $0x1,%rcx") using hc
    host_checked_step (host_member0 54 (by decide)) at 212 encodedWidth 2
      opcodeAST parse("je serialize_u300") using hc
    simpa [StatusFlags.from_result, target, Effects.All, hostScanState] using
      empty (by simp [significantCount]) old _
  | succ n ih =>
    intro within old flags empty nonempty
    have readLimb : Mem.loadInt s.dmem
        (s.regs.rax.toBitVec + BitVec.ofNat 64 (8 * n)) 8 =
        some ((words[n]?.getD 0#64).toNat : Int) := by
      simpa [List.getElem?_eq_getElem (show n < words.length by omega)] using
        stored ⟨n, by omega⟩
    apply host_scan_step e base hc s old _ flags n (by omega) readLimb P
    · intro isZero fl
      apply ih (by omega) _ fl
      · intro h old fl'
        exact empty (by simpa [significantCount, isZero] using h) old fl'
      · intro h fl'
        simpa [significantCount, isZero] using
          nonempty (by simpa [significantCount, isZero] using h) fl'
    · intro isNonzero fl
      simpa [significantCount, isNonzero] using
        nonempty (by simp [significantCount, isNonzero]) fl

/-- Pointer-zero immediates bypass scanning; borrowed operands retain R9's
physical length while RCX is initialized to that length plus one. -/
theorem host_entry_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (small : s.regs.rax.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 308))
    (large : s.regs.rax.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      (hostScanState s (s.regs.r9.toBitVec + 1) s.regs.rdx.toBitVec flags, base + 208)) :
    Eventually (step e) P (s, base + 196) := by
  have target := hc.targets ("serialize_u308", 308) (by decide)
  host_checked_step (host_member0 49 (by decide)) at 196 encodedWidth 3
    opcodeAST parse("testq %rax,%rax") using hc
  constructor <;>
    host_checked_step (host_member0 50 (by decide)) at 199 encodedWidth 2
      opcodeAST parse("je serialize_u308") using hc
  all_goals
    by_cases isZero : s.regs.rax.toBitVec = 0#64
    · simpa [StatusFlags.from_result, isZero, target, Effects.All] using small isZero _
    · simp [StatusFlags.from_result, isZero, Effects.All]
      host_checked_step (host_member0 51 (by decide)) at 201 encodedWidth 4
        opcodeAST parse("leaq 0x1(%r9),%rcx") using hc
      host_checked_step (host_member0 52 (by decide)) at 205 encodedWidth 3
        opcodeAST [.instr (.regular .W64 .W64 (.nop 3))] using hc
      simpa [hostScanState] using large isZero _

/-- PC229--233 accepts exactly one significant limb; any other positive count
falls through to the original host-failure block at PC235. -/
theorem host_count_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (one : s.regs.rdx.toBitVec = 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 305))
    (many : s.regs.rdx.toBitVec ≠ 1#64 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 235)) :
    Eventually (step e) P (s, base + 229) := by
  have target := hc.targets ("serialize_u305", 305) (by decide)
  host_checked_step (host_member0 59 (by decide)) at 229 encodedWidth 4
    opcodeAST parse("cmpq $0x1,%rdx") using hc
  host_checked_step (host_member0 60 (by decide)) at 233 encodedWidth 2
    opcodeAST parse("je serialize_u305") using hc
  by_cases isOne : s.regs.rdx.toBitVec = 1#64
  · simpa [StatusFlags.from_result, isOne, target, Effects.All] using one isOne _
  · simpa [StatusFlags.from_result, isOne, Effects.All] using many isOne _

/-- An all-zero scan still reads limb zero when physical storage is nonempty.
Only a physically empty borrowed value branches to the zero shortcut. -/
theorem host_zero_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (empty : s.regs.r9.toBitVec = 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 385))
    (nonempty : s.regs.r9.toBitVec ≠ 0 → ∀ flags, Eventually (step e) P
      ({s with status := flags}, base + 305)) :
    Eventually (step e) P (s, base + 300) := by
  have target := hc.targets ("serialize_u385", 385) (by decide)
  host_checked_step (host_member1 6 (by decide)) at 300 encodedWidth 3
    opcodeAST parse("testq %r9,%r9") using hc
  constructor <;>
    host_checked_step (host_member1 7 (by decide)) at 303 encodedWidth 2
      opcodeAST parse("je serialize_u385") using hc
  all_goals
    by_cases isZero : s.regs.r9.toBitVec = 0#64
    · simpa [StatusFlags.from_result, isZero, target, Effects.All] using empty isZero _
    · simpa [StatusFlags.from_result, isZero, Effects.All] using nonempty isZero _

theorem host_empty_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (P : MachineState → Prop)
    (next : ∀ flags, Eventually (step e) P (hostValueState s 0 flags, base + 388)) :
    Eventually (step e) P (s, base + 385) := by
  host_checked_step (host_member1 21 (by decide)) at 385 encodedWidth 3
    opcodeAST parse("xorl %r9d,%r9d") using hc
  constructor <;> simpa [hostValueState] using next _

theorem host_load_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (limb : BitVec 64)
    (stored : Mem.loadInt s.dmem s.regs.rax.toBitVec 8 = some (limb.toNat : Int))
    (P : MachineState → Prop)
    (next : Eventually (step e) P (hostValueState s limb s.status, base + 308)) :
    Eventually (step e) P (s, base + 305) := by
  host_checked_step (host_member1 8 (by decide)) at 305 encodedWidth 3
    opcodeAST parse("movq (%rax),%r9") using hc
  serialize_load stored
  simpa [hostValueState] using next

/-- The existing significant-count/value theorem at one machine word. -/
theorem host_fits_iff (operand : NatOperand) :
    operand.wordCount ≤ 1 ↔ operand.value < 2 ^ 64 := by
  simpa only [Nat.mul_one] using operand.wordCount_le_iff_value_lt 1

theorem host_failure_iff (operand : NatOperand) :
    1 < operand.wordCount ↔ 2 ^ 64 ≤ operand.value := by
  have fits := host_fits_iff operand
  omega

private theorem host_low_value (words : List (BitVec 64))
    (fits : Limbs.value words < 2 ^ 64) :
    Limbs.value words = (words[0]?.getD 0).toNat := by
  cases words with
  | nil => simp [Limbs.value]
  | cons limb rest =>
    simp only [Limbs.value] at fits ⊢
    simp only [List.getElem?_cons_zero, Option.getD_some]
    omega

private theorem host_large_read (s : MachineData) (pointer : BitVec 64)
    (words : List (BitVec 64))
    (stored : (NatOperand.large pointer words).At (widthLoad s.dmem))
    (i : Nat) (within : i < words.length) :
    Mem.loadInt s.dmem (pointer + BitVec.ofNat 64 (8 * i)) 8 =
      some ((words[i]?.getD 0).toNat : Int) := by
  have observed := stored.2.2.2 ⟨i, within⟩
  change widthLoad s.dmem (pointer.toNat + 8 * i) 8 = some words[i].toNat at observed
  simpa only [List.getElem?_eq_getElem within, Option.getD_some, width_address] using
    widthLoad_eq s.dmem _ _ _ observed

/-- Actual native host-size conversion, PC196 to the original three cuts.
All assumptions describe the starting registers and borrowed memory. Failure is
exactly unrepresentability in 64 bits. Every normal success reaches PC308 with
R9 equal to the whole natural, not its truncation. Large [] instead executes
PC300/303/385 and reaches PC388 with zero, which fits every unsigned capacity.
No canonical-storage or logical-limb-count premise is required. -/
theorem host_cps (e : Executable) (base : Int64) (hc : CodeAt e base)
    (s : MachineData) (operand : NatOperand)
    (pointer : s.regs.rax.toBitVec = operand.pointer)
    (payload : s.regs.r9.toBitVec = operand.payload)
    (stored : operand.At (widthLoad s.dmem)) (P : MachineState → Prop)
    (failure : 2 ^ 64 ≤ operand.value → ∀ t, HostFrame s t →
      Eventually (step e) P (t, base + 235))
    (capacity : operand.value < 2 ^ 64 → ∀ t, HostFrame s t →
      t.regs.r9.toNat = operand.value → Eventually (step e) P (t, base + 308))
    (empty : operand.value = 0 → ∀ t, HostFrame s t →
      t.regs.r9.toBitVec = 0 → operand.value ≤ t.regs.r13.toNat →
      Eventually (step e) P (t, base + 388)) :
    Eventually (step e) P (s, base + 196) := by
  cases operand with
  | small limb =>
    have pp : s.regs.rax.toBitVec = 0 := pointer
    have pv : s.regs.r9.toBitVec = limb := payload
    have valueEq : (NatOperand.small limb).value = limb.toNat := by
      simp only [NatOperand.value, NatOperand.words, Limbs.value, Nat.mul_zero, Nat.add_zero]
    apply host_entry_cps e base hc s P
    · intro _ flags
      apply capacity
      · rw [valueEq]
        exact limb.isLt
      · exact host_status_frame s flags
      · change s.regs.r9.toBitVec.toNat = (NatOperand.small limb).value
        rw [pv, valueEq]
    · intro nonzero
      exact False.elim (nonzero pp)
  | large p words =>
    have pp : s.regs.rax.toBitVec = p := pointer
    have pv : s.regs.r9.toBitVec = BitVec.ofNat 64 words.length := payload
    have bound : words.length + 1 < 2 ^ 64 := by
      have physical := stored.2.2.1
      omega
    have pnonzero : p ≠ 0 := by
      intro zero
      have positive := stored.1
      simp [zero] at positive
    have countBound : sigWords words < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (sigWords_le_length words) (by omega)
    have borrowed : (NatOperand.large p words).value < 2 ^ 64 →
        0 < words.length → ∀ t, HostFrame s t →
        Eventually (step e) P (t, base + 305) := by
      intro fits nonempty t frame
      have pt : t.regs.rax.toBitVec = p :=
        (frame.registers .rax (by decide) (by decide) (by decide)).trans pp
      have readLow : Mem.loadInt t.dmem t.regs.rax.toBitVec 8 =
          some ((words[0]?.getD 0).toNat : Int) := by
        simpa only [frame.memory, pt, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero] using host_large_read s p words stored 0 nonempty
      apply host_load_cps e base hc t (words[0]?.getD 0) readLow P
      apply capacity fits
      · exact frame.trans (host_value_frame t _ _)
      · change (words[0]?.getD 0).toNat = Limbs.value words
        exact (host_low_value words fits).symm
    apply host_entry_cps e base hc s P
    · intro zero
      exact False.elim (pnonzero (pp.symm.trans zero))
    · intro _ flags
      have plusOne : s.regs.r9.toBitVec + 1 = BitVec.ofNat 64 (words.length + 1) := by
        change s.regs.r9.toBitVec + 1#64 = BitVec.ofNat 64 (words.length + 1)
        rw [pv, BitVec.ofNat_add]
      rw [plusOne]
      apply host_scan_cps e base hc s words bound
      · intro i
        have observed := host_large_read s p words stored i.val i.isLt
        rw [List.getElem?_eq_getElem i.isLt, Option.getD_some] at observed
        change Mem.loadInt s.dmem (s.regs.rax.toBitVec + BitVec.ofNat 64 (8 * i.val)) 8 =
          some (words[i.val].toNat : Int)
        simpa only [pp] using observed
      · exact Nat.le_refl _
      · intro zero old flags'
        have fits : (NatOperand.large p words).value < 2 ^ 64 := by
          apply (host_fits_iff _).1
          change significantCount words words.length ≤ 1
          omega
        apply host_zero_cps e base hc _ P
        · intro noWords flags''
          have nil : words = [] := by
            apply List.length_eq_zero_iff.mp
            have noWordsNat := congrArg BitVec.toNat noWords
            change s.regs.r9.toBitVec.toNat = 0 at noWordsNat
            rw [pv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at noWordsNat
            exact noWordsNat
          have valueZero : (NatOperand.large p words).value = 0 := by
            subst words
            rfl
          apply host_empty_cps e base hc _ P
          intro flags'''
          apply empty valueZero
          · exact (host_scan_frame s _ old flags').trans
              ((host_status_frame _ flags'').trans (host_value_frame _ _ flags'''))
          · rfl
          · omega
        · intro hasWords flags''
          have nonempty : 0 < words.length := by
            by_cases positiveLength : 0 < words.length
            · exact positiveLength
            · have lenZero : words.length = 0 := by omega
              apply False.elim (hasWords _)
              change s.regs.r9.toBitVec = 0
              rw [pv, lenZero]
              rfl
          apply borrowed fits nonempty
          exact (host_scan_frame s _ old flags').trans (host_status_frame _ flags'')
      · intro positive flags'
        apply host_count_cps e base hc _ P
        · intro one flags''
          have countOne : sigWords words = 1 := by
            have natural := congrArg BitVec.toNat one
            change (BitVec.ofNat 64 (sigWords words)).toNat = 1 at natural
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound] at natural
            exact natural
          have fits : (NatOperand.large p words).value < 2 ^ 64 := by
            apply (host_fits_iff _).1
            change sigWords words ≤ 1
            omega
          have nonempty : 0 < words.length := by
            have countWithin := sigWords_le_length words
            omega
          apply borrowed fits nonempty
          exact (host_scan_frame s _ _ flags').trans (host_status_frame _ flags'')
        · intro notOne flags''
          have many : 1 < (NatOperand.large p words).wordCount := by
            change 1 < sigWords words
            by_cases manyWords : 1 < sigWords words
            · exact manyWords
            · have countOne : sigWords words = 1 := by
                change 0 < sigWords words at positive
                omega
              apply False.elim (notOne _)
              change BitVec.ofNat 64 (sigWords words) = 1#64
              rw [countOne]
          apply failure ((host_failure_iff _).1 many)
          exact (host_scan_frame s _ _ flags').trans (host_status_frame _ flags'')

end SszX86.Serialize
