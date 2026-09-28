import SszX86.EmitUintWidthSteps

namespace SszX86.Emit.Uint.Instructions
open Kraken.X64.Parser
open BoolCodec UintCodec
open UintCodec.Large (get put putF compare subFlags shift)

abbrev low8 (v : BitVec 64) : BitVec 8 := v.setWidth 8
abbrev low32 (v : BitVec 64) : BitVec 64 := (v.setWidth 32).setWidth 64

def test {w : Nat} (s : MachineData) (v : BitVec w) (flags : StatusFlags) : MachineData :=
  {s with status := StatusFlags.from_result v {cf := false, af := flags.af, of := false}}

def store (s : MachineData) (p : BitVec 64) (byteCount : Nat) (value : Int) : MachineData :=
  {s with dmem := Mem.storeInt s.dmem p byteCount value}

def readAddress (pc : Nat) (s : MachineData) : BitVec 64 :=
  match pc with
  | 597 => get s .r12 + 8
  | 602 => get s .r12 + 16
  | 644 => get s .rdi + get s .rcx * 8
  | 912 | 958 => get s .rdi + get s .r10 * 8
  | _ => 0

def Read (pc : Nat) (s : MachineData) (limb : BitVec 64) : Prop :=
  pc = 597 ∨ pc = 602 ∨ pc = 644 ∨ pc = 912 ∨ pc = 958 →
    Mem.loadInt s.dmem (readAddress pc s) 8 = some (limb.toNat : Int)

def storeAddress (pc : Nat) (s : MachineData) : BitVec 64 :=
  match pc with
  | 655 | 1147 => get s .rbx
  | 928 => get s .r14 + get s .rax + 1
  | 988 => get s .r14 + get s .rax
  | 1085 => get s .r14 + get s .r8
  | 1099 => get s .r14 + get s .r8 + 1
  | 1144 => get s .r14
  | _ => 0

def storeWidth (pc : Nat) : Nat := if pc = 655 ∨ pc = 1147 then 8 else 1

def Writable (pc : Nat) (s : MachineData) : Prop :=
  pc = 655 ∨ pc = 928 ∨ pc = 988 ∨ pc = 1085 ∨ pc = 1099 ∨ pc = 1144 ∨ pc = 1147 →
    ∃ old, Mem.loadInt s.dmem (storeAddress pc s) (storeWidth pc) = some old

/-- These are bounded summaries of literal image rows. Live comparison and TEST
flags are retained; only flags dead before their next use are universally hidden. -/
def instruction (pc : Nat) (s : MachineData) (limb : BitVec 64)
    (flags : StatusFlags) : MachineData :=
  match pc with
  | 583 => compare s (get s .rsi) (get s .r9)
  | 592 => test s (get s .rsi) flags
  | 597 => put s .rdi limb
  | 602 | 644 => put s .rdx limb
  | 607 => test s (get s .rdi) flags
  | 616 | 876 => compare s (get s .rsi) 1
  | 626 | 886 | 903 | 1045 => putF s .rax 0 flags
  | 628 | 1015 => put s .rcx (get s .rax)
  | 631 | 1018 => putF s .rcx (get s .rcx >>> (3 : Nat)) flags
  | 635 | 1022 => compare s (get s .rcx) (get s .rdx)
  | 653 => putF s .rsi 0 flags
  | 655 | 1147 => store s (get s .rbx) 8 (get s .rsi).toInt
  | 893 => put s .r8 (get s .rsi)
  | 896 => putF s .r8 (get s .r8 &&& 0xfffffffffffffffe#64) flags
  | 900 | 1042 => putF s .r9 0 flags
  | 912 => put s .r10 limb
  | 916 | 979 | 1073 => put s .rcx (low32 (get s .r9))
  | 919 | 982 | 1076 => putF s .rcx
      ((get s .rcx).replaceLow (low8 (get s .rcx) &&& 0x30#8)) flags
  | 922 | 1089 => putF s .rcx
      ((get s .rcx).replaceLow (low8 (get s .rcx) ||| 8#8)) flags
  | 925 | 1092 => putF s .r10 (get s .r10 >>> shift s) flags
  | 928 => store s (get s .r14 + get s .rax + 1) 1 (low8 (get s .r10)).toInt
  | 933 => putF s .rax (get s .rax + 2) flags
  | 937 | 1104 => putF s .r9 (get s .r9 + 16) flags
  | 941 => compare s (get s .r8) (get s .rax)
  | 946 => put s .r10 (get s .rax)
  | 949 => putF s .r10 (get s .r10 >>> (3 : Nat)) flags
  | 953 | 992 => compare s (get s .r10) (get s .rdx)
  | 958 => put s .r11 limb
  | 976 => putF s .r11 0 flags
  | 985 => putF s .r11 (get s .r11 >>> shift s) flags
  | 988 => store s (get s .r14 + get s .rax) 1 (low8 (get s .r11)).toInt
  | 997 => putF s .r10 0 flags
  | 1063 => put s .r10 0
  | 1002 | 1113 => test s ((get s .rsi).setWidth 8 &&& 1) flags
  | 1012 => putF s .r14 (get s .r14 + get s .rax) flags
  | 1031 => putF s .rdx 0 flags
  | 1035 => put s .rdi (get s .rsi)
  | 1038 => putF s .rdi (get s .rdi &&& 0xfffffffffffffffe#64) flags
  | 1056 => put s .r8 (get s .rax)
  | 1059 | 1128 => compare s (get s .rax) 8
  | 1069 => put s .r10 (if s.status.cf then get s .rdx else get s .r10)
  | 1079 => put s .rax (get s .r10)
  | 1082 => putF s .rax (get s .rax >>> shift s) flags
  | 1085 => store s (get s .r14 + get s .r8) 1 (low8 (get s .rax)).toInt
  | 1095 => put s .rax (get s .r8 + 2)
  | 1099 => store s (get s .r14 + get s .r8 + 1) 1 (low8 (get s .r10)).toInt
  | 1108 => compare s (get s .rdi) (get s .rax)
  | 1119 => putF s .r14 (get s .r14 + get s .r8) flags
  | 1122 => putF s .r14 (get s .r14 + 2) flags
  | 1126 => putF s .rcx 0 flags
  | 1132 => put s .rdx (if s.status.cf then get s .rdx else get s .rcx)
  | 1136 => putF s .rax (((get s .rax).setWidth 32 <<< (3 : Nat)).setWidth 64) flags
  | 1139 => put s .rcx (low32 (get s .rax))
  | 1141 => putF s .rdx (get s .rdx >>> shift s) flags
  | 1144 => store s (get s .r14) 1 (low8 (get s .rdx)).toInt
  | _ => s

def next (pc : Nat) (s : MachineData) : Nat :=
  match pc with
  | 583 => 586
  | 586 => if !s.status.cf && !s.status.zf then 1615 else 592
  | 592 => 595
  | 595 => if s.status.zf then 653 else 597
  | 597 => 602
  | 602 => 607
  | 607 => 610
  | 610 => if s.status.zf then 876 else 616
  | 616 => 620
  | 620 => if s.status.zf then 626 else 893
  | 626 => 628
  | 628 => 631
  | 631 => 635
  | 635 => 638
  | 638 => if s.status.cf then 644 else 1031
  | 644 => 648
  | 648 => 1136
  | 653 => 655
  | 655 => 658
  | 658 => 1593
  | 876 => 880
  | 880 => if s.status.zf then 886 else 1035
  | 886 => 888
  | 888 => 1136
  | 893 => 896
  | 896 => 900
  | 900 => 903
  | 903 => 905
  | 905 => 946
  | 912 => 916
  | 916 => 919
  | 919 => 922
  | 922 => 925
  | 925 => 928
  | 928 => 933
  | 933 => 937
  | 937 => 941
  | 941 => 944
  | 944 => if s.status.zf then 1002 else 946
  | 946 => 949
  | 949 => 953
  | 953 => 956
  | 956 => if s.status.cf then 958 else 976
  | 958 => 962
  | 962 | 976 => 979
  | 979 => 982
  | 982 => 985
  | 985 => 988
  | 988 => 992
  | 992 => 995
  | 995 => if s.status.cf then 912 else 997
  | 997 => 1000
  | 1000 => 916
  | 1002 => 1006
  | 1006 => if s.status.zf then 1147 else 1012
  | 1012 => 1015
  | 1015 => 1018
  | 1018 => 1022
  | 1022 => 1025
  | 1025 => if s.status.cf then 644 else 1031
  | 1031 => 1033
  | 1033 => 1136
  | 1035 => 1038
  | 1038 => 1042
  | 1042 => 1045
  | 1045 => 1047
  | 1047 => 1056
  | 1056 => 1059
  | 1059 => 1063
  | 1063 => 1069
  | 1069 => 1073
  | 1073 => 1076
  | 1076 => 1079
  | 1079 => 1082
  | 1082 => 1085
  | 1085 => 1089
  | 1089 => 1092
  | 1092 => 1095
  | 1095 => 1099
  | 1099 => 1104
  | 1104 => 1108
  | 1108 => 1111
  | 1111 => if s.status.zf then 1113 else 1056
  | 1113 => 1117
  | 1117 => if s.status.zf then 1147 else 1119
  | 1119 => 1122
  | 1122 => 1126
  | 1126 => 1128
  | 1128 => 1132
  | 1132 => 1136
  | 1136 => 1139
  | 1139 => 1141
  | 1141 => 1144
  | 1144 => 1147
  | 1147 => 1150
  | 1150 => 1593
  | _ => pc

end SszX86.Emit.Uint.Instructions
