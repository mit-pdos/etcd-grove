/-
`(*grpc.ClientConn).NewStream(ctx, desc, method, opts...)` (grpc-go, assumed: `stream.go`).

Users: the generated streaming stubs (`kVClient.RangeStream`, `watchClient.Watch`,
`leaseClient.LeaseKeepAlive`, `maintenanceClient.Snapshot`, 3h), hence W0's `RangeStream`, 1b's
`remoteWatchAt_watch`, 1c's `remoteLeaseAt_keepAlive`.

Why true: `NewStream` calls the stream interceptor, if one was dialed, with grpc's `newClientStream`
as the streamer; else the streamer. The streamer opens one stream to an address its resolver
reported (`streamerOk_call`), sending the headers (the metadata) once; messages then go in order,
intact, once each way.

Changes: from `specs-ref/Spec/google_golang_org/grpc/ClientConn__NewStream.lean`: over the method's
registered `StreamSpec` and contents (`notes/grpc-stream-spec.md`'s proposal, with fixed message
types and no caller-built model); no size premise.

Margin: none beyond `ownErr`'s.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `cc.NewStream(ctx, desc, method, opts...)`: the connection's stream interceptor around grpc's
streamer (WP form). -/
def ClientConn.NewStream.spec : Prop :=
  ∀ (cc : Loc) (A : GoString → IProp GF) (ui si : Option val) (R : MD → IProp GF)
    (ctx : GoInterface) (desc : Loc) (m : GoString) (opts : GoSlice) (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ∗ connAt cc A ui si R ∗
    (∀ str : val, streamerOk cc A R str -∗
      match si with
      | none => WP (App (App (App (App (App (Val str) (Val #ctx)) (Val #desc)) (Val #cc)) (Val #m))
          (Val #opts)) {{ Ψ }}
      | some f => WP (App (App (App (App (App (App (Val f) (Val #ctx)) (Val #desc)) (Val #cc))
          (Val #m)) (Val str)) (Val #opts)) {{ Ψ }}) ⊢
  WP (App (App (App (App (Val (cc @!! go.GoType.PointerType google_golang_org.grpc.ClientConn.ty @!! go!"NewStream"))
    (Val #ctx)) (Val #desc)) (Val #m)) (Val #opts)) {{ Ψ }}

end spec

end Grpc
end EtcdGrove
end Perennial
