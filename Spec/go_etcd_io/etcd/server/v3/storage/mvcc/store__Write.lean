/-
`store.Write` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

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

/-- `s.Write(trace)` opens a write transaction at the committed log, for one revision token:
`s.mu` held shared and the batch transaction locked (the writer's resources) until `End`.
`LockInsideApply` runs the store's post-lock hook `f` under the lock (invariant `P`, `hookIs`)
on the caller's `Pre`, by the caller's triple: its `Q` is the caller's. -/
abbrev mvcc.store.Write.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (P Pre Q : IProp GF) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ mvcc.revToken γ ∗
      mvcc.hookIs γ P f ∗ Pre ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
  {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
      (∃ ilog : mvcc.Log, mvcc.isTxnWrite mw s γ ilog [] (W64 0) (W64 0) (W64 0)) ∗ Q }}

end spec

end EtcdGrove
end Perennial
