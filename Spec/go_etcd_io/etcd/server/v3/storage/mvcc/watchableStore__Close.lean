/-
`watchableStore.Close` (`watchable_store.go`). Lean-first (no Rocq counterpart); see `InvWatchSync.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

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

/-- `s.Close()`, with the right to close the store (`wsCloser`, once: `New` returns it): closes the
stop channel (the loops return), waits for the loops (`s.wg.Wait()`), and closes the inner store
(`store.Close`, the trust boundary), returning its `nil`. -/
abbrev mvcc.watchableStore.Close.spec : Prop :=
  ∀ (s st : Loc) (γ : mvcc.WsNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ∗ mvcc.wsCloser s st }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"Close")) (Val #()))
  {{ RET #(GoInterface.nil); True }}

end spec

end EtcdGrove
end Perennial
