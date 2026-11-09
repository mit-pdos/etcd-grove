/-
The trust boundary of `reflect.MakeSlice` (see its spec).
-/
module

public import Spec.reflect.MakeSlice

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

axiom reflect.MakeSlice.wp_proof : reflect.MakeSlice.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
