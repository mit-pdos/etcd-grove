/-
`conversion.EnforcePtr(obj)` of a non-nil pointer `p : *T` (`k8s.io/apimachinery`, names-only:
`reflect.ValueOf(obj)`, its kind checked, `.Elem()`): the addressable `Value` of the `T` at `p`.

The trust boundary: an axiom, `Proof/k8s_io/apimachinery/pkg/conversion/EnforcePtr.lean` (`reflect` is names-only; the reasoning
principles of `Proof/reflect/Values.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.reflect.Values
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI reflectM

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [reflect.Assumptions]

/-- See the file header. -/
abbrev conversion.EnforcePtr.spec : Prop :=
  ∀ (T : go.GoType) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion ∗ ⌜p ≠ null⌝ }}
    (App (Val (@! k8s_io.apimachinery.pkg.conversion.EnforcePtr))
      (Val #(interface.mkOk (go.GoType.PointerType T) #p : GoInterface)))
  {{ (v : _root_.Perennial.reflect.Value) (err : GoInterface), RET (PairV #v #err);
      ⌜err = GoInterface.nil ∧ reflElem v T p⌝ }}

end spec

end EtcdGrove
end Perennial
