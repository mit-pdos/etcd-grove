/-
`watchStream.Cancel` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream

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

/-- **`ws.Cancel(id)`**: `nil` (the watcher of `id` cancelled) or `ErrWatcherNotExist` (no
watcher of that id, or the stream closed). -/
abbrev mvcc.watchStream.Cancel.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : GName) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ }}
    (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Cancel")) (Val #id))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ globalAddr ErrWatcherNotExist ↦□ err }}

end spec

end EtcdGrove
end Perennial
