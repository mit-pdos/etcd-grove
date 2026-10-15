/-
`watchableStore.progress` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
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

/-- `s.progress(w)`: the `watchable` contract's `progress` (`progressIfSync` of `w` alone, with
its id). -/
abbrev mvcc.watchableStore.progress.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (w : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ (mvcc.storeWatchParams s st γ).IW w ∗
      mvcc.watchReader s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"progress")) (Val #w))
  {{ RET #(); mvcc.watchReader s st γ }}

end spec

end EtcdGrove
end Perennial
