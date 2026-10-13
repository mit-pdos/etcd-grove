/-
`watchableStore.notify` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.notify(rev, evs)` under `s.mu` (the lock's state `σ` at the sole writer's log `ilog`, its
synced watchers delivered at most up to `ilog`'s length), for the events `evs` of the pending
revision `rev = ilog.length` (sealed: the history's lower bound of `ilog ++ [pend]`): each synced
watcher with events gets them in one response (one revision: the `revs != 1` panic is
unreachable) and is then delivered up to `rev + 1`, or, if its channel is full, becomes a victim
with its batch; the others are delivered up to `rev + 1` with nothing to send. -/
abbrev mvcc.watchableStore.notify.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (σ : mvcc.WsState) (ilog : mvcc.Log)
    (pend : List mvcc.Change) (evs : GoSlice) (dq : DFrac) (es : List Loc) (evm : List mvcc.EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.watchStoreBody s γ 1 σ ∗
      ⌜σ.Lmu = ilog ∧ σ.syncedBelow ilog.length ∧ ilog.length + 2 < 2 ^ 63 ∧ ilog ≠ []⌝ ∗
      monoListLbOwn γ.st.idx.hist (mvcc.histOf (ilog ++ [pend])) ∗
      evs ↦*{dq} es ∗ ([∗list] x ∈ es.zip evm, mvcc.evIs x.1 x.2) ∗
      ⌜es.length = evm.length ∧ evm = mvcc.evsOfRevM ilog.length (mvcc.stateAfter ilog) pend⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"notify"))
      (Val #(W64 ilog.length))) (Val #evs))
  {{ RET #(); evs ↦*{dq} es ∗ ∃ σ' : mvcc.WsState, mvcc.watchStoreBody s γ 1 σ' ∗
      ⌜σ'.Lmu = ilog ∧ σ'.syncedAbove (ilog.length + 1)⌝ }}

end spec

end EtcdGrove
end Perennial
