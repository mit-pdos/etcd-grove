/-
gRPC's robustness driver's `client` command: its package fact, `True` (no variables).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client
end Perennial
