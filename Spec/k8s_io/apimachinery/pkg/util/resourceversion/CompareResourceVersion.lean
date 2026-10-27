/-
`CompareResourceVersion(a, b)` (`resourceversion.go`): the comparison of two well-formed resource
versions as decimal numbers (`cmpNat (decVal a) (decVal b)`: `-1`, `0`, `1`) and a nil error; an
`InvalidResourceVersion` error (and `0`) if either is not well formed (`wellFormed`: `""` and
`"0"` are not). Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI k8s_io.apimachinery.pkg.util.resourceversion

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

/-- The error `CompareResourceVersion` returns for the malformed version `rv`. -/
abbrev invalidRVErr (rv : GoString) : GoInterface :=
  interface.mkOk InvalidResourceVersion.ty #(InvalidResourceVersion.mk rv)

/-- What `CompareResourceVersion(a, b)` returns: if both are well formed, their values'
comparison and `nil`; else `0` and the `InvalidResourceVersion` of the first malformed one. -/
def compareRV (a b : GoString) : w64 × GoInterface :=
  if wellFormed a then
    if wellFormed b then (cmpNat (decVal a) (decVal b), interface.nil)
    else (W64 0, invalidRVErr b)
  else (W64 0, invalidRVErr a)

/-- `CompareResourceVersion(a, b)`: `compareRV a b`. -/
abbrev CompareResourceVersion.spec : Prop :=
  ∀ (a b : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion }}
    (App (App (Val (@! CompareResourceVersion)) (Val #a)) (Val #b))
  {{ RET (PairV #(compareRV a b).1 #(compareRV a b).2); True }}

end spec

end resourceversion
end EtcdGrove
end Perennial
