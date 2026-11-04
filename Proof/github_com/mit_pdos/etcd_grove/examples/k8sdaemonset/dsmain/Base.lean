/-
The package-initialization instance of the DaemonSet driver `examples/k8sdaemonset/dsmain`: its
fact is `True` (no package variable). Lean-first; track C of the DaemonSet run.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Base
public import Proof.k8s_io.kubernetes.Base
public import Proof.k8s_io.client_go.informers.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance github_com_mit_pdos_etcd_grove_examples_k8sdaemonset_dsmain_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain :=
  define_is_pkg_init iprop(True)
instance github_com_mit_pdos_etcd_grove_examples_k8sdaemonset_dsmain_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain
end Perennial
