/-
Lean-first (no Rocq counterpart).

Package initialization instance of the conditional-authorization driver (`examples/k8s/authz`,
project `k8s-authz-driver`): its fact is `True` (it has no package variables).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.authz
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Base
public import Proof.math.rand.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.k8s.authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance github_com_mit_pdos_etcd_grove_examples_k8s_authz_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz :=
  define_is_pkg_init iprop(True)
instance github_com_mit_pdos_etcd_grove_examples_k8s_authz_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.authz :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.k8s.authz
end Perennial
