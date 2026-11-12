/-
`watchStream.RequestProgressAll` (watcher.go). Lean-first (no Rocq counterpart); see
`InvWatchStream.lean` and the mvcc API (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

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

/-- **`ws.RequestProgressAll`**: the API's contract at `*watchStream`
(`mvcc.api.WatchStream.RequestProgressAll.contract`, `Spec/.../mvcc/Api.lean`; stage 2 of the mvcc
API, 2026-11-05: the stream's internal spec replaced by the API's, strict M1). -/
abbrev mvcc.watchStream.RequestProgressAll.spec : Prop :=
  ∀ w : Loc, mvcc.api.WatchStream.RequestProgressAll.contract (GF := GF)
    (go.GoType.PointerType watchStream.ty) #w

end spec

end EtcdGrove
end Perennial
