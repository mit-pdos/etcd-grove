/-
The trust boundary: `Spec/k8s_io/apimachinery/pkg/util/resourceversion/isWellFormed.lean` (gap C1,
`notes/k8s-clientgo-goose.md`: names only, its `range` over a string untranslated). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.resourceversion.isWellFormed

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

axiom isWellFormed.wp_proof : isWellFormed.spec (GF := GF) (hG := hG)

end proof

end resourceversion
end EtcdGrove
end Perennial
