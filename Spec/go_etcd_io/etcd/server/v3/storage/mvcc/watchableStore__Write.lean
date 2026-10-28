/-
`watchableStore.Write` (`watchable_store_txn.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.Write(trace)` opens a write transaction of the inner store (`store.Write`) for the sole
writer at its committed log `L` (one of its revision tokens; its tokens and certificate pin the
transaction's committed log to `L`; the trace not `nil`, as `store.Write` takes it) and wraps it with the store, for `End` to notify. As
`store.Write`, the inner `LockInsideApply` runs the store's post-lock hook `f` (invariant `P`,
`hookIs`) on the caller's `Pre`: its `Q` is the caller's. -/
abbrev mvcc.watchableStore.Write.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (trace : Loc) (L : mvcc.Log) (P Pre Q : IProp GF)
    (f : val) (te : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.storeReader st γ.st ∗ mvcc.storeWT γ.st ∗
      mvcc.watchWriter γ L ∗
      ⌜L.length + 4 ≤ 2 ^ 63⌝ ∗ ⌜trace ≠ null⌝ ∗
      mvcc.hookIs γ.st P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      traceutil.ownTrace trace te }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Write")) (Val #trace))
  {{ (tw : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw);
      mvcc.isWatchTxnWrite tw s st γ trace L [] (W64 0) (W64 0) (W64 0) ∗ Q ∗ mvcc.hookIs γ.st P f }}

end spec

end EtcdGrove
end Perennial
