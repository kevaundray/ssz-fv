import SszArm.SerializePostLogic

namespace SszArm.Serialize

open SszNative.Serialize (Desc Value Error)
open UintCodec (widthLoad)

/-- Semantic rejection, scratch exhaustion and output failure remain distinct;
none of them is removed from the original-entry contract. -/
theorem Post.refines {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (physical : value.Physical) :
    ∃ result writes,
      ResultAt (widthLoad t) (Args.ofEntry s).result.toNat result ∧
      SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat writes ∧
      (SszNative.Serialize.eraseResult (result.map (fun _ => writes)) =
          .ok (Ssz.serialize desc.erase value.erase) ∨
        result = .error (.arithmetic .scratchExhausted) ∨
        result = .error .outputTooSmall) := by
  exact ⟨(outcome s (Args.ofEntry s) desc value).outcome.result,
    (outcome s (Args.ofEntry s) desc value).writes, post.result, post.bytes,
    SszNative.Serialize.serialize_refines desc value (Args.ofEntry s).capacity.toNat
      (arenaOf s (Args.ofEntry s)) physical⟩

/-- The exact written prefix is the pinned SSZ encoding, not merely a byte count. -/
theorem Post.success_encoding {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (physical : value.Physical) (count : Nat)
    (success : (outcome s (Args.ofEntry s) desc value).outcome.result = .ok count) :
    ∃ bytes, Ssz.serialize desc.erase value.erase = .ok bytes ∧ bytes.size = count ∧
      count ≤ (Args.ofEntry s).capacity.toNat ∧
      SszNative.ByteView.BytesAt (widthLoad t) (Args.ofEntry s).output.toNat bytes ∧
      widthLoad t (Args.ofEntry s).result.toNat 8 = some count ∧
      widthLoad t ((Args.ofEntry s).result.toNat + 64) 4 = some 0 := by
  have encoding := SszNative.Serialize.serialize_success desc value (Args.ofEntry s).capacity.toNat
    (arenaOf s (Args.ofEntry s)) physical count success
  have result := post.result
  simp only [success, ResultAt] at result
  exact ⟨(outcome s (Args.ofEntry s) desc value).writes,
    encoding.1, encoding.2.1, encoding.2.2, post.bytes, result.1, result.2⟩

/-- Every failure precedes emission. Even a failure after committed measurement
allocations leaves the entire original output capacity untouched. -/
theorem Post.failure_output {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) (reason : Error)
    (failure : (outcome s (Args.ofEntry s) desc value).outcome.result = .error reason) :
    (outcome s (Args.ofEntry s) desc value).writes = #[] ∧
      ∀ index, index < (Args.ofEntry s).capacity.toNat →
        t.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index) =
          s.mem ((Args.ofEntry s).output + BitVec.ofNat 64 index) := by
  have empty := SszNative.Serialize.serialize_failure_writes desc value
    (Args.ofEntry s).capacity.toNat (arenaOf s (Args.ofEntry s)) reason failure
  change (outcome s (Args.ofEntry s) desc value).writes = #[] at empty
  refine ⟨empty, ?_⟩
  intro index high
  exact post.tail index (by simp only [empty, Array.size_empty, Nat.zero_le]) high

/-- The final arena and every allocation observation are those produced by
measurement, including host/capacity errors after successful retained planning. -/
theorem Post.retained {s t : ArmState} {desc : Desc} {value : Value}
    (post : Post s t desc value) :
    (read_mem_bytes 8 ((Args.ofEntry s).arena + 16#64) t).toNat =
        (measured s (Args.ofEntry s) desc value).used ∧
      ∀ call ∈ (measured s (Args.ofEntry s) desc value).calls,
        NatDivision.WrittenAt (widthLoad t) call := by
  have resources := outcome_resources s (Args.ofEntry s) desc value
  refine ⟨post.cursor.trans resources.1, ?_⟩
  intro call member
  exact post.written call (resources.2.symm ▸ member)

end SszArm.Serialize
