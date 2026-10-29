/-
`(*clientv3.retryAuthClient).Authenticate(ctx, in, opts...)` (`client/v3/retry.go`; the auth plan's
C1, 2026-10-28). Lean-first (no Rocq counterpart).
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

/-- `rac.Authenticate(ctx, in, opts...)` on a `*retryAuthClient` over a stub on a connection to
`addr`: `rac.ac.Authenticate(ctx, in, opts...)` (no retry option added): the call's answer
(`authnCallOut`). -/
abbrev retryAuthClient.Authenticate.spec : Prop :=
  ∀ (rac conn : Loc) (addr : List GoString)
    (Spec : GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse)
    (Φ : GoString → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (m : (pbAuthenticateRequest (GF := GF)).M) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryAuthAt rac conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcs addr authnMethod Spec ∗ □ ▷ Spec m Φ ∗ ctxOk ctx cd ∗
      (pbAuthenticateRequest (GF := GF)).send inp m ∗ opts ↦*□ vs ∗ callOptsOk vs }}
    (App (App (App (Val (rac @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryAuthClient.ty @!!
        go!"Authenticate")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (pbAuthenticateRequest (GF := GF)).send inp m ∗ authnCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
