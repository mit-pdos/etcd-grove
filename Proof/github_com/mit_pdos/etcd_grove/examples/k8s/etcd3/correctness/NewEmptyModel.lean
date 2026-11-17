module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewEmptyModel

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem NewEmptyModel.wp_proof : NewEmptyModel.spec (GF := GF) (hG := hG) := by
  intro pfx nf nlf v
  wp_start as -
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string
    k8s_io.apimachinery.pkg.runtime.Object.ty) as %il Hil
  iapply HΦ
  iframe «$r0» Hil

end proof

end k8s_correctness
end EtcdGrove
end Perennial
