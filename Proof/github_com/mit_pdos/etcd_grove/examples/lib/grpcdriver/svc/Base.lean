/-
gRPC's robustness driver's service `svc` (`examples/lib/grpcdriver/svc`): its package fact, `True`
(its variable `Driver_ServiceDesc` is read by the server's proof from what the initializer stores).
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

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
