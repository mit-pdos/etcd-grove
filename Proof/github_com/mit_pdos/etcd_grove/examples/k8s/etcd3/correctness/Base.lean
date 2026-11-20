/-
Lean-first (no Rocq counterpart).

The package facts of the driver's copy of Kubernetes' checker (`examples/k8s/etcd3/correctness`,
k8s 7g, `notes/k8s-7g-scope.md`) and of the two packages it calls that are translated names only
here, go-cmp's `cmp` and the standard library's `maps`: none (`True`). The copy has no package
variables, and the two names-only packages none that the checker reads.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance maps_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.maps :=
  define_is_pkg_init iprop(True)
instance maps_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.maps :=
  build_get_is_pkg_init_wf

instance cmp_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.github_com.google.go_cmp.cmp :=
  define_is_pkg_init iprop(True)
instance cmp_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.google.go_cmp.cmp :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness
end Perennial
