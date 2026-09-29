import SszArm.CodecEmitContract
import SszArm.CodecSerializeGeometry
import SszArm.SerializeEmitEntry

namespace SszArm.Codec.Serialize

/-- Unlike the primitive ABI projection, the recursive emitter observes x3:
it points to the retained Plan in the still-live wrapper activation. -/
def Args.emit (args : Args) (count : Nat) : Emit.Args :=
  ⟨args.result, args.descriptor, args.value, args.plan,
    args.output, BitVec.ofNat 64 count, args.bodySP⟩

 theorem emitter_entry_args (base : BitVec 64) (s : ArmState) (args : Args) (count : Nat)
    (registers : SszArm.Serialize.Registers s args)
    (payload : r (.GPR 5#5) s = BitVec.ofNat 64 count) :
    Emit.Args.ofEntry (SszArm.Serialize.emitterEntry base s) = args.emit count := by
  rcases registers with ⟨result, output, value, descriptor, capacity, stack⟩
  unfold SszArm.Serialize.emitterEntry
  change Emit.Args.ofEntry (SszArm.Serialize.block base
    [.p648, .p652, .p656, .p660, .p664, .p668] s) = args.emit count
  simp [Emit.Args.ofEntry, Args.emit, SszArm.Serialize.block, SszArm.Serialize.Op.effect,
    SszArm.Serialize.put, SszArm.Serialize.next, state_simp_rules,
    SszArm.Serialize.Args.plan, result, output, value, descriptor, stack, payload]

/-- The actual six setup/BL instructions pass exactly the measured prefix and
the original retained Plan. No fake standalone allocation/size entry is used. -/
theorem emitter_entry_correct (base : BitVec 64) (s : ArmState) (args : Args) (count : Nat)
    (registers : SszArm.Serialize.Registers s args)
    (payload : r (.GPR 5#5) s = BitVec.ofNat 64 count)
    (code : SszArm.Serialize.CodeAt s base) (error : read_err s = .None)
    (aligned : CheckSPAlignment s) (pc : read_pc s = base + 648#64) :
    run 6 s = SszArm.Serialize.emitterEntry base s ∧
      Emit.Args.ofEntry (SszArm.Serialize.emitterEntry base s) = args.emit count ∧
      read_pc (SszArm.Serialize.emitterEntry base s) = base + SszArm.Serialize.emitOffset ∧
      r (.GPR 30#5) (SszArm.Serialize.emitterEntry base s) = base + 672#64 :=
  ⟨SszArm.Serialize.emitterEntry_run s base code error aligned pc,
    emitter_entry_args base s args count registers payload,
    SszArm.Serialize.emitterEntry_pc base s, SszArm.Serialize.emitterEntry_lr base s⟩

end SszArm.Codec.Serialize
