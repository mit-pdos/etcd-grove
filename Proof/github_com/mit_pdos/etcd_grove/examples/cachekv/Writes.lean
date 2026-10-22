/-
**The writers' vocabulary** (2026-10-20). Lean-first (no Rocq counterpart).

watchkv's (`Proof/.../watchkv/Writes.lean`) with the client's half of the KV ghost state in the
client's invariant with its revision as a monotone counter (`client.kvClientInv`), not watchkv's
plain `wkKV`: the cache's gets need the ranges' updates with a floor (`client.kvRangeAu_of_inv`),
and the writers' updates open the same invariant.

* `ckKV γr γm`: `client.kvClientInv γr γm`; each writer's update (`kvOpAu1` of its put, `put_au`)
  opens it and moves the counter; the workload lets the client deposit every put of the plan.
* `okFact E p`: watchkv's, at cachekv's `putRec`: the revision is at least `2` and is the put of
  the key and value (`watchkv.revAt`), from the reply (`okFact_of_reply`).
* `wsInv w E`: the lock invariant of the log `w`: its slice of successful Puts, each with `okFact`.
* The Put itself is the client package's `client.client_Put_rep` (`client/v3/ClientPutGet.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Writes
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Writes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.cachekv

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The client's `etcdKV`, in the client's invariant (with its revision's counter at `γm`). -/
abbrev ckKV (γr : ReadNames) (γm : GName) : IProp GF := client.kvClientInv γr γm

/-- **A writer's update** for the put of `k ↦ v` (fired at most once): it steps the state and
moves the counter. -/
theorem put_au (γr : ReadNames) (γm : GName) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = watchkv.workload P) (k v : GoString) (h : (k, v) ∈ P) :
    client.kvClientInv (GF := GF) γr γm ⊢
      kvOpAu1 γr.kv (.put (client.putKeyOp k v)) (fun _ => iprop(True)) := by
  have Hm := client.kvClientN_mask
  iintro #Hinv
  unfold kvOpAu1 kvAu1
  isplitr
  · ipureintro; rw [hwl]; exact Or.inl ⟨_, rfl, watchkv.putOk_putKeyOp P k v h⟩
  iauintro
  unfold atomic_acc
  iunfold client.kvClientInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ, Hmn⟩
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists σ; iframe Hσ Hmn
    imodintro; itrivial
  · iintro Hσ
    imod Hclose2 with -
    imod (mono_nat_own_update (GF := GF) (γ := γm)
      (kvOpStep (.put (client.putKeyOp k v)) σ).rev
      (client.kvOpStep_rev (.put (client.putKeyOp k v)) σ)) $$ Hmn with ⟨Hmn, -⟩
    imod Hclose $$ [Hσ Hmn] with -
    · inext; iexists _; iframe Hσ Hmn
    imodintro; itrivial

/- **What the program knows of a successful Put it logged**, from its reply, and **the log's lock
invariant**: the shared start's (`common/Writes.lean`). -/
export common (okFact okFact_persistent okFact_of_reply wsInv)

end defs

end cachekv
end EtcdGrove
end Perennial
