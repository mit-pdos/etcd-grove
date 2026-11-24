/- Lean-first (no Rocq counterpart).

# `svc._Driver_Fail_Handler`'s proof

The generated unary handler's body (`unaryHandlerImpl`, `etcdserverpb/UnaryHandlerLemmas.lean`) at
`DriverServer`, `*StringValue` and `Fail`: `wp_unaryHandlerOwnMd` (the build checks the body).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc._Driver_Fail_Handler
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.UnaryHandlerLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove google_golang_org.protobuf.types.known

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem _Driver_Fail_Handler.wp_proof : _Driver_Fail_Handler.spec (GF := GF) (hG := hG) :=
  wp_unaryHandlerOwnMd _Driver_Fail_Handler DriverServer.ty wrapperspb.StringValue.ty
    wrapperspb.StringValue.ty go!"Fail" go!"/grpcdriver.Driver/Fail"

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
