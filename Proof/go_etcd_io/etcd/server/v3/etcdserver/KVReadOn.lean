/-
**The KV invariant's readers in the auth mode `on`** (the auth plan's E2u, 2026-10-26;
`notes/decisions.md`, "E2u of the auth plan"): the counterparts over E2q's mode-`on` invariants
(`kvInvOn`, `kvCertInvOn`, `KVApplyOn.lean`) of what the server's readers learn from the mode-off
ones: the KV invariant's step at a commit (`kvInvOn_facts_snoc`,
`kvInvOn_commit_granted`, `kvInvOn_commit_keep`), where a client's update fires: a granted plain
write steps the KV state by its request, an admin entry or a refused one keeps it. (The `lean`
merge, R6, 2026-11-07: the readers of mvcc's certificate `certOk`, `kv_cert_read_on` and
`kv_cert_floor_on`, deleted: unused since the request path reads the store's raft witness `E.Nx`.)

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver


section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The mode-`on` KV invariant's pure facts, one committed entry on** (`kvInv_facts_snoc`'s):
the entry meets the committer's obligation (`commitOkOn`: admitted and determinate at the model's
state after `L`), and its index the next. -/
theorem kvInvOn_facts_snoc (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (L : List EntryModel) (e : EntryModel)
    (hok : plainLogOn L ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) L ∧ srvIdxOkW γ.ai0 L ∧
      uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] ∧ γ.raft.authOn = true ∧
      kvLogSmall γk L)
    (hidx' : srvIdxOkW γ.ai0 (L ++ [e]))
    (hc : commitOkOn γk.c0 γk.ch0 (st₀, γk.log0) L e) (hsz : L.length + 1 < 2 ^ 61) :
    plainLogOn (L ++ [e]) ∧ detLogOn γk.c0 γk.ch0 (st₀, γk.log0) (L ++ [e]) ∧
      srvIdxOkW γ.ai0 (L ++ [e]) ∧ uint.Z γk.c0 ≤ uint.Z γ.ai0 ∧
      γk.ch0 = apply.alarmChain true false false ∧ γk.log0 ≠ [] ∧ γ.raft.authOn = true ∧
      kvLogSmall γk (L ++ [e]) := by
  obtain ⟨hp, hd, -, hc0, hch, h0, hao, hsm⟩ := hok
  obtain ⟨hp', hd'⟩ := logOn_snoc γk.c0 γk.ch0 (st₀, γk.log0) L e hp hd hc
  exact ⟨hp', hd', hidx', hc0, hch, h0, hao, kvLogSmall_snoc γk L e hsm hsz⟩

/-- **A granted plain write's commit fires its client's update** (the ghost step at the commit, in
the mode `on`): the invariant's half of the state's ghost variable at the committed log `L`'s model
and a client's `etcdKV` at `σ` agree, and both move to the request's step, which is the model's
state after `L ++ [e]` (`kvModelOn_snoc_granted`). -/
theorem kvInvOn_commit_granted (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (rq : apply.IRRModel) (σ : KVState)
    (hch : γk.ch0 = apply.alarmChain true false false)
    (h0 : γk.log0 ≠ []) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z γk.c0 < uint.Z e.index)
    (hna : apply.needAdminPermission rq = false)
    (hg : kvGranted (kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) L).1 rq) (hpc : plainCover rq) :
    ⊢ ghostVar (GF := GF) γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) -∗ etcdKV γk σ ==∗
      ⌜σ = kvStateOf (kvModelOn γk st₀ L)⌝ ∗
      ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ (L ++ [e]))) ∗
      etcdKV γk (kvReqStep rq σ) := by
  iintro Hσ Hc
  iunfold etcdKV at Hc
  ihave %Hag := ghostVar_agree γk.st _ _ _ _ $$ Hσ Hc
  have hst := kvModelOn_snoc_granted γk st₀ L e rq hch h0 ht hd hdec hidx hna hg hpc
  imod ghostVar_update_halves (kvReqStep rq σ) γk.st _ _ $$ Hσ Hc with ⟨Hσ, Hc⟩
  imodintro
  isplitr
  · ipureintro; exact Hag.symm
  rw [hst, Hag]
  iframe Hσ
  iunfold etcdKV
  iexact Hc

/-- **An entry that keeps the KV log keeps the state** (an admin entry, `kvModelOn_snoc_admin`, or
a refused KV entry, `kvModelOn_snoc_refused`): the invariant's half moves to `L ++ [e]` unchanged,
no client's update fires. -/
theorem kvInvOn_commit_keep (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (e : EntryModel) (hk : kvModelOn γk st₀ (L ++ [e]) = kvModelOn γk st₀ L) :
    ghostVar (GF := GF) γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ L)) ⊢
      ghostVar γk.st (1 : Qp).half (kvStateOf (kvModelOn γk st₀ (L ++ [e]))) := by
  rw [hk]

end lemmas

end EtcdGrove
end Perennial
