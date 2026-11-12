/-
`as.AuthStatus(ctx, r)` (`v3rpc/auth.go`): the server's `AuthStatus` through the `Authenticator` interface, its
error through `togRPCError`. Lean-first (no Rocq counterpart); the auth plan's A3, the API layer
(2026-10-24), vocabulary `InvAuthServer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvAuthServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`as.AuthStatus(ctx, r)`**: the server's `AuthStatus` (the interface value the `*AuthServer` holds is the
server, `authServerIs`; the method as the contract `authInnerOk`, over the caller's `P` answering
`Q`), then `togRPCError` on its error; the outcome `authWrapOut`: the server's response with
`Q resp nil`, or `nil` and a non-nil error with `Q null` of the server's error. -/
abbrev v3rpc.AuthServer.AuthStatus.spec : Prop :=
  ∀ (p s : Loc) (ctx : GoInterfaceOk) (r : Loc) (P : IProp GF) (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.authServerIs p s ∗ P ∗ v3rpc.authInnerOk s go!"AuthStatus" (GoInterface.ok ctx) r P Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.AuthServer.ty @!! go!"AuthStatus"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); v3rpc.authWrapOut Q resp err }}

end spec

end EtcdGrove
end Perennial
