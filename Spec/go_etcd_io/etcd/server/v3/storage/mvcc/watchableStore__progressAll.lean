/-
`watchableStore.progressAll` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchStore.lean`.
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

/-- `s.progressAll(m)`: the `watchable` contract's `progressAll` (`progressIfSync` with
`InvalidWatchID`). -/
abbrev mvcc.watchableStore.progressAll.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames) (m : Loc) (dq : DFrac) (M : GMap w64 Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ m ↦${dq} M ∗
      □ (∀ (id : w64) (w : Loc), ⌜M !! id = some w⌝ -∗ (mvcc.storeWatchParams s st γ).IW w) ∗
      mvcc.watchReader s st γ }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"progressAll")) (Val #m))
  {{ (b : Bool), RET #b; m ↦${dq} M ∗ mvcc.watchReader s st γ }}

end spec

end EtcdGrove
end Perennial
