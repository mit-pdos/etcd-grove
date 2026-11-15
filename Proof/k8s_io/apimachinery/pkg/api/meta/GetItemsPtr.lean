/-
The trust boundary of `apimeta.GetItemsPtr` (see its spec).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.GetItemsPtr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.«meta».Assumptions]
variable [dpkg : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

axiom apimeta.GetItemsPtr.wp_proof : apimeta.GetItemsPtr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
