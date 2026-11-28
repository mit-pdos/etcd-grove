/-
**`grpc_health_v1`'s package fact** (grpc-health, 2026-11-26): its service descriptor
`Health_ServiceDesc` (`health_grpc.pb.go`), read-only, with its methods and stream exactly: the methods
`Check` and `List`, the server stream `Watch`. Its initializer allocates and sets the descriptor (a
`grpc.ServiceDesc` literal, translated: until then a skipped variable) and runs the package's `init`
(the do-nothing trusted model, `TrustedCode/google_golang_org/grpc/health/grpc_health_v1.lean`).
`RegisterHealthServer` registers the descriptor (`RegisterHealthServer.wp_proof`). Until 2026-11-26 the
package's fact was `True` (`v3rpc/BaseGrpc.lean`). As the grpcdriver's `drvDescs`
(`examples/lib/grpcdriver/svc/Base.lean`).
-/
module

public import GeneratedProof.google_golang_org.grpc.health.grpc_health_v1
public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace google_golang_org.grpc.health.grpc_health_v1

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The health service's `ServiceDesc`** (see the file header). -/
abbrev healthDescs : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
    go_etcd_io.etcd.cache.v3.pbDescIs (globalAddr Health_ServiceDesc) go!"grpc.health.v1.Health"
      (interface.mkOk (go.GoType.PointerType HealthServer.ty) #(null : Loc)) mds sds ∗
    ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
        [(go!"Check", @! _Health_Check_Handler), (go!"List", @! _Health_List_Handler)] ∧
      sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) =
        [(go!"Watch", @! _Health_Watch_Handler, true, false)]⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 :=
  define_is_pkg_init healthDescs
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 :=
  build_get_is_pkg_init_wf

/-- `grpc_health_v1`'s package fact. -/
theorem healthDescs_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1 ⊢ healthDescs := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.google_golang_org.grpc.health.grpc_health_v1

end init

end google_golang_org.grpc.health.grpc_health_v1
end Perennial
