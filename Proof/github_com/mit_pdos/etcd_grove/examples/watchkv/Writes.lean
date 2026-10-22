/-
**The writers' vocabulary** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

* `wkKV γr`: the client's half of the KV ghost state (`etcdKV`), in an invariant of the program's,
  so that each writer's update (`kvOpAu1` of its put, `put_au`) can fire at the server's apply;
  the workload lets the client deposit every put of the plan (`putOk`).
* `okFact E p`: what the program knows of a successful Put it logged, `p` (its reply's header
  revision, key and value): the revision is at least `2` and is the put of the key and value
  (`revAt`), from the reply (`okFact_of_reply`: `putReplied`'s certificate of the log after, whose
  last revision is the put's change, `client.put_applied_log`).
* `wsInv w E`: the lock invariant of the log `w`: its slice of successful Puts, each with
  `okFact`.
* The Put itself is the client package's `client.client_Put_rep` (`client/v3/ClientPutGet.lean`,
  D31): the reply's message and `putReplied`, on a client that sends a write at most once.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Writes
public import Proof.go_etcd_io.etcd.client.v3.CacheClient
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.watchkv

/-- The program's KV invariant's namespace. -/
def wkN : Namespace := nroot .@ "watchkv_kv"

theorem wkN_mask : (↑wkN : CoPset) ⊆ (⊤ \ ↑(nroot.@"raft_commit")) \ ↑(nroot.@"server_kv") := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The client's `etcdKV`, in the program's invariant. -/
def wkKV (γr : ReadNames) : IProp GF := inv wkN (∃ σ : KVState, etcdKV γr.kv σ)

instance wkKV_persistent (γr : ReadNames) : Persistent (wkKV (GF := GF) γr) := by
  unfold wkKV; infer_instance

/-- The plan's put of `k ↦ v` as the client sends it. -/
theorem putOk_putKeyOp (P : List (GoString × GoString)) (k v : GoString) (h : (k, v) ∈ P) :
    putOk P (client.putKeyOp k v) := by
  unfold putOk client.putKeyOp txn.putOpOf
  simp [h]

/-- **A writer's update** for the put of `k ↦ v` (fired at most once): it steps the state. -/
theorem put_au (γr : ReadNames) (P : List (GoString × GoString)) (hwl : γr.kv.wl = workload P)
    (k v : GoString) (h : (k, v) ∈ P) :
    wkKV (GF := GF) γr ⊢ kvOpAu1 γr.kv (.put (client.putKeyOp k v)) (fun _ => iprop(True)) := by
  have Hm := wkN_mask
  iintro #Hinv
  unfold kvOpAu1 kvAu1
  isplitr
  · ipureintro; rw [hwl]; exact Or.inl ⟨_, rfl, putOk_putKeyOp P k v h⟩
  iauintro
  unfold atomic_acc
  iunfold wkKV at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, Hσ⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑wkN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists σ; iexact Hσ
    imodintro; itrivial
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ] with -
    · inext; iexists _; iexact Hσ
    imodintro; itrivial

/- **What the program knows of a successful Put it logged**, from its reply, and **the log's lock
invariant**: the shared start's (`common/Writes.lean`). -/
export common (okFact okFact_persistent okFact_of_reply wsInv)

end defs

end watchkv
end EtcdGrove
end Perennial
