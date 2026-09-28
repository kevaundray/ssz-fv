import SszX86.EmitBodies
import SszX86.EmitFinish

namespace SszX86.Emit
open SszNative.Serialize

/-- The actual private codec::emit entry, complete through the caller RET, for
all seven primitive descriptors. Premises describe only original arguments,
physical byte ownership, the exact linked emit image and its real memcpy image. -/
theorem program_correct (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat)
    (owned : Owned s base desc value buffer ra written) :
    Eventually (step e) (Post s desc value buffer ra written) (s, base) := by
  apply eventually_trans (step e) _ _ _
    (entry_correct e base hc s desc value buffer ra written owned)
  rintro ⟨body, pc⟩ ⟨entryPC, anchors, tag⟩
  dsimp only at entryPC
  subst pc
  apply eventually_trans (step e) _ _ _
    (bodies_run e base hc helper s body desc value buffer ra written owned anchors tag)
  rintro ⟨final, pc⟩ ⟨successPC, post⟩
  dsimp only at successPC
  subst pc
  exact finish_runs e base hc s body final desc value buffer ra written owned anchors post

/-- Exact private execution refines the pinned SSZ serializer, not a second
encoding model. The post includes ABI restoration, original borrowed bytes,
the exact success record, and the untouched output capacity tail. -/
theorem program_refines (e : Executable) (base : Int64) (hc : CodeAt e base)
    (helper : MemcpyCodeAt e (base + 110736))
    (s : MachineData) (desc : Desc) (value : Value)
    (buffer ra : BitVec 64) (written : Nat)
    (owned : Owned s base desc value buffer ra written) :
    Eventually (step e) (fun final => Post s desc value buffer ra written final ∧
      Ssz.serialize desc.erase value.erase = .ok (emit desc value) ∧
      (emit desc value).size = written) (s, base) := by
  apply eventually_weaken (step e) _ _ _ _
    (program_correct e base hc helper s desc value buffer ra written owned)
  intro final post
  exact ⟨post, owned.valid.pinned, owned.valid.emitted_size⟩

end SszX86.Emit
