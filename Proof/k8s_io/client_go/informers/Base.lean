/-
The packages of client-go's informer factory (`k8s.io/client-go/informers` and its group packages
`informers/apps`, `informers/core`): their package-initialization facts, `True` (no package
variable). The versions' packages (`informers/{apps,core}/v1`) have theirs in
`Proof/k8s_io/kubernetes/Base.lean`. Lean-first; the DaemonSet run's track A.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import GeneratedProof.k8s_io.client_go.informers
public import GeneratedProof.k8s_io.client_go.informers.apps
public import GeneratedProof.k8s_io.client_go.informers.core

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace k8s_io.client_go.informers

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance k8s_io_client_go_informers_apps_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers.apps :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_apps_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers.apps :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_informers_core_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers.core :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_core_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers.core :=
  build_get_is_pkg_init_wf

instance k8s_io_client_go_informers_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.client_go.informers :=
  define_is_pkg_init iprop(True)
instance k8s_io_client_go_informers_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.client_go.informers :=
  build_get_is_pkg_init_wf

end init

end k8s_io.client_go.informers
end Perennial
