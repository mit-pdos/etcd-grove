/-
`runtime.Decode(d, data)` (`k8s.io/apimachinery/pkg/runtime/codec.go`; translated with its body;
stage E of k8s 7f-6, the watch path's `decodeObj`) of a decoder whose
`Decode(data, nil, nil)` gives `R` of its object and error (`P` its precondition): that object and
error. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]

/-- See the file header. -/
abbrev runtime.Decode.spec : Prop :=
  ∀ (di : GoInterfaceOk) (dsl : GoSlice) (P : IProp GF) (R : GoInterface → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗ P ∗
      (∀ Ψ : val → IProp GF, P -∗
        ▷ (∀ (x : GoInterface) (g : Loc) (err : GoInterface), R x err -∗
          Ψ (PairV (PairV #x #g) #err)) -∗
        WP (App (App (App (Val #(methods di.ty go!"Decode" di.v)) (Val #dsl)) (Val #null))
          (Val #(interface.nil : GoInterface))) {{ Ψ }}) }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.runtime.Decode)) (Val #(GoInterface.ok di)))
      (Val #dsl))
  {{ (x err : GoInterface), RET (PairV #x #err); R x err }}

end spec

end EtcdGrove
end Perennial
