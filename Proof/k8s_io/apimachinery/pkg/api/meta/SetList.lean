/-
The trust boundary of `meta.SetList` (see its spec, `Spec.k8s_io.apimachinery.pkg.api.meta.SetList`; reviewed:
`notes/axiom-review/k8s-7g-trust.md`).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.meta.SetList

@[expose] public section

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

/-- **Trust-boundary assumption** (an axiom, not a proof): `meta.SetList` on the driver's `*ObjList` and `*Obj` objects sets `Items` to a fresh non-nil slice of the objects' structs and returns `nil`; why that is true of Go is in the
spec's file header, with its Go tests. -/
axiom meta.SetList.wp_proof_objList : meta.SetList.spec_objList (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
