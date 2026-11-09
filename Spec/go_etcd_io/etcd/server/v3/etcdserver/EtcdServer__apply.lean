/-
`(*EtcdServer).apply(es, ep, raftAdvancedC)` (`server.go:1917-1968`): apply committed entries in
order; for each, decide whether its effects go to the backend (`ShouldApplyV3`: past the consistent
index), set the applying index, apply it (`applyEntryNormal`, or decode and `applyConfChange` and
answer the conf change's waiter), and record the applied index and term.

**Users**: `applyEntries` (`server.go:1229`). Snippets `apply.go` (`ReqWriteAnswered`,
`ReqConfChangeAnswered`, `ReqReplayBelowCI`).

**Proof sketch**. Loop invariant at entry `i` (index `k = a + i + 1`): `applyAt s γ ep p (k - 1) c ai`.
`consistIndex.ConsistentIndex()` (`Cindex.consistentIndex.ConsistentIndex.spec`, the thread's
`ciWriter`): `c`. `applyV3 c k`: `SetConsistentApplyingIndex(k, term)` (`ai := k`). The entry's type
is `EntryNormal` or `EntryConfChange` (`committed_types`: the "unknown entry type" panic is
unreachable). Normal: `applyEntryNormal.spec`. Conf change: `pbutil.MustUnmarshalMessage` decodes it
(R1's `committedLb_confDecodes`: a legacy `ConfChange`), `applyConfChange.spec`, then
`w.Trigger(cc.Id, &confChangeResponse{s.cluster.Members(), raftAdvancedC, err})` (2c's wait
registry: its predicate for a conf change's id is given by the response with `advancedAt r rac
last`, the members read from the membership view, `req/` 2c). `setAppliedIndex(k)`
(`setAppliedIndex.spec`: `srvApplied s γ k` from the thread), `setTerm`.

**Changes** from `specs-ref`'s `apply.spec` (the write-token pool, `kvAppliedM`, the restart point's
ghost log, `dvView`, the receipts' bound): over `applyAt`; the replay below the consistent index is
the general case (`applyV3`), not a restart window.

**Margin**: `shouldStop` is `true` exactly when a conf change removed this member; the post does not
say so (`applyEntries` only uses it to schedule the stop, which is safe either way).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Apply committed entries** `ents` (from index `a + 1`, the applied index): the thread is applied
through `a + |ents|`; returns the last entry's term and index. -/
def EtcdServer.apply.spec : Prop :=
  ∀ (s : Loc) (γ : Names) (id : w64) (ep : Loc) (p : Progress) (a c ai : Nat) (es : GoSlice)
    (ents : List Raft.LogEntry) (l : List Raft.LogEntry) (rac : Loc) (k : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNode s γ id ∗ applyAt s γ ep p a c ai ∗ Raft.entriesRO es (a + 1) ents ∗
      Raft.committedLb γ.raft l ∗
      advancedAt (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"r" s) rac k ∗
      ⌜ents ≠ [] ∧ (l.drop a).take ents.length = ents ∧ a + ents.length ≤ k⌝ }}
    (App (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!!
      go!"apply")) (Val #es)) (Val #ep)) (Val #rac))
  {{ (t i : w64) (stop : Bool), RET (PairV (PairV #t #i) #stop);
      ∃ c' ai', applyAt s γ ep p (a + ents.length) c' ai' ∗
      ⌜uint.nat i = a + ents.length ∧ (ents.getLast?).map (·.term) = some t⌝ }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
