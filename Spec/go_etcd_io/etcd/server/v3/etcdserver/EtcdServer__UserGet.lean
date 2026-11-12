/-
`s.UserGet(ctx, r)` (`v3_server.go`): `raftRequest` on `&pb.InternalRaftRequest{AuthUserGet: r}`. Lean-first
(no Rocq counterpart); the auth plan's A3, the API layer (2026-10-24), vocabulary `AuthEntry.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.UserGet(ctx, r)`** for the request `r` holding the name `name` (`apply.authUserGetIs`, what the apply package's request model records of it): `raftRequest` on the request
`irrUserGet name` (`&pb.InternalRaftRequest{AuthUserGet: r}`), taken as the contract `authRaftOk` for the
response type `*pb.AuthUserGetResponse` (`AuthEntry.lean`: the proposal path is proved for the KV requests
only, `reqPropOk`), over the caller's `P` answering `Q`; the outcome `authEntryOut`: the applied
response (typed) with `Q resp nil`, or `nil` and the error with `Q null err`. The admin check of
this request is the apply layer's (`apply.adminPass`, for the header's principal). -/
abbrev EtcdServer.UserGet.spec : Prop :=
  ∀ (s : Loc) (ctx : GoInterfaceOk) (r : Loc) (name : GoString) (P : IProp GF)
    (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ apply.authUserGetIs r name ∗ P ∗
      authRaftOk s ctx (irrUserGet name) etcdserverpb.AuthUserGetResponse.ty P Q }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"UserGet"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); applyErrIs err ∗ authEntryOut Q resp err }}

end spec

end EtcdGrove
end Perennial
