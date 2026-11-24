/-
gRPC's robustness driver (`examples/lib/grpcdriver`, notes/library-drivers.md): its package fact,
`True` (its variable `reached` is read by the client's proof from what the initializer stores).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
