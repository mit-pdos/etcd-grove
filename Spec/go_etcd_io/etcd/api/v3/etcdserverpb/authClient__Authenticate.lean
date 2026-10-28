/-
`(*etcdserverpb.authClient).Authenticate(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Auth stub; the auth plan's C1, 2026-10-28). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Authenticate(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`authStubAt`),
for a spec `Spec` the server registered for the method and the caller's persistent `□ ▷ Spec m Φ`:
`Invoke` of `"/etcdserverpb.Auth/Authenticate"` with `grpc.StaticMethod()` before the options, into a new
response: the call's answer (`authnCallOut`, the run's `Φ` of the reply's token); the request comes back. -/
abbrev etcdserverpb.authClient.Authenticate.spec : Prop :=
  ∀ (ac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse) (Φ : GoString → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp : Loc) (m : (pbAuthenticateRequest (GF := GF)).M)
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ authStubAt ac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr authnMethod Spec ∗ □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthenticateRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (ac @!! go.GoType.PointerType go_etcd_io.etcd.api.v3.etcdserverpb.authClient.ty @!! go!"Authenticate"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthenticateRequest (GF := GF)).send inp m ∗ authnCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
