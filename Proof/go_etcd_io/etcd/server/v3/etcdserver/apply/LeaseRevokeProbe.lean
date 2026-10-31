/-
**LeaseRevoke through the apply chain: the Draft's probes** (`notes/lease-revoke-plan.md`).
Imported by nothing; no `axiom`, no `sorry`. What the derivation of the Revoke clause
(`LeaseRevokeDraft.lean`, `deriveRevokeStmt`) is riskiest at, proved ahead:

- `kvWriter_open`: the KV's writer over a watchable store opens to the watchable store's sole
  writer (`watchWriter`) at the names its `wlogOwn` holds, where the range deleter's contract
  (`rdAt`'s, at every name set: R2) applies, and closes at any log the commit leaves `soleLog`.
- `leaseDels_none`: a lease no key of the state has deletes nothing (the not-found case, and a
  live lease with no key: the log stays).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LeaseRevokeDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

namespace apply

section probes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- **The KV's writer, opened at the watchable store** (R2's probe). -/
theorem kvWriter_open (s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (hw : γ.watchQ = true)
    (X : Loc → mvcc.WsNames → IProp GF) :
    txn.kvWriter s γ log ∗ □ (∀ (ws : Loc) (γw : mvcc.WsNames), mvcc.isWatchableStore ws s γw -∗ X ws γw) ⊢
      ∃ (ws : Loc) (γw : mvcc.WsNames), ⌜γw.st = γ ∧ txn.soleLog log⌝ ∗ X ws γw ∗
        mvcc.watchWriter γw log ∗ mvcc.writerFrag γ ∗
        (∀ log' : mvcc.Log, ⌜txn.soleLog log'⌝ -∗ mvcc.watchWriter γw log' -∗ mvcc.writerFrag γ -∗
          txn.kvWriter s γ log') := by
  iintro ⟨Hkw, #HX⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfrag⟩
  iunfold txn.soleWriter at Hsw
  icases Hsw with ⟨#Hc, Htok, %Hs⟩
  icases (txn.wlogOwn_watch s γ log hw).1 $$ Hwl with ⟨%ws, %γw, %hγ, #Hws, Hhalf, -⟩
  subst hγ
  iexists ws, γw
  isplitr
  · ipureintro; exact ⟨rfl, Hs.1⟩
  isplitr
  · iapply HX $$ Hws
  isplitl [Htok Hhalf]
  · iunfold mvcc.watchWriter
    iframe Hc Hhalf
    unfold mvcc.wBudget
    unfold txn.soleBudget
    iexact Htok
  iframe Hfrag
  iintro %log' %Hs' Hww Hfrag
  iunfold mvcc.watchWriter at Hww
  icases Hww with ⟨#Hc', Htok', Hhalf'⟩
  iunfold txn.kvWriter
  iframe Hfrag
  isplitl [Htok']
  · iunfold txn.soleWriter
    iframe Hc'
    isplitl
    · unfold mvcc.wBudget at *
      unfold txn.soleBudget
      iexact Htok'
    · ipureintro; exact ⟨Hs', Hs.2⟩
  iapply (txn.wlogOwn_watch s γw.st log' hw).2
  iexists ws, γw
  iframe Hws Hhalf' Hc'
  ipureintro; rfl

end probes

/-- **No key on the lease, no deletion** (the not-found case's probe). -/
theorem leaseDels_none [GooseExts] (s : List EtcdKv) (id : w64) (h : ∀ v ∈ s, v.lease ≠ id) :
    mvcc.leaseDels s id = [] := by
  unfold mvcc.leaseDels mvcc.leaseDelKeys
  split
  · rfl
  · rw [List.filter_eq_nil_iff.2 (fun v hv => by simpa using h v hv)]; rfl

end apply
end EtcdGrove
end Perennial
