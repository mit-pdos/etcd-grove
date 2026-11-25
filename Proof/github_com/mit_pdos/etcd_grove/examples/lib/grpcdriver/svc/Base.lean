/-
gRPC's robustness driver's service `svc` (`examples/lib/grpcdriver/svc`): its package fact,
`drvDescs`: its service descriptor `Driver_ServiceDesc` (a generated literal, never written), with its
service name, handler type, and its methods and streams exactly, with their generated handlers and
stream kinds (as etcdserverpb's `etcdserverpbDescs`): what `RegisterService` (the server) and
`NewStream` (the client, a stream's descriptor) read.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.protobuf.types.known.wrapperspb.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The driver's `ServiceDesc`** (see the file header). -/
abbrev drvDescs : IProp GF :=
  iprop(∃ (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
    go_etcd_io.etcd.cache.v3.pbDescIs (globalAddr Driver_ServiceDesc) go!"grpcdriver.Driver"
      (interface.mkOk (go.GoType.PointerType DriverServer.ty) #(null : Loc)) mds sds ∗
    ⌜mds.map (fun md => (md.MethodName', (#md.Handler' : val))) =
        [(go!"Echo", @! _Driver_Echo_Handler), (go!"Fail", @! _Driver_Fail_Handler),
         (go!"Meta", @! _Driver_Meta_Handler)] ∧
      sds.map (fun sd => (sd.StreamName', (#sd.Handler' : val), sd.ServerStreams', sd.ClientStreams')) =
        [(go!"ServerStream", @! _Driver_ServerStream_Handler, true, false),
         (go!"ClientStream", @! _Driver_ClientStream_Handler, false, true),
         (go!"Bidi", @! _Driver_Bidi_Handler, true, true)]⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc :=
  define_is_pkg_init drvDescs
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc :=
  build_get_is_pkg_init_wf

/-- `svc`'s package fact. -/
theorem drvDescs_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc ⊢
      drvDescs := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF)
    pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

end init

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
