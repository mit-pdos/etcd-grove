/-
`storage.AnnotateInitialEventsEndBookmark(obj)` (`k8s.io/apiserver/pkg/storage/util.go:92`;
translated with its body; stage E of k8s 7f-6, the watch path's initial-events-end bookmark) of an
object whose dynamic type is a `metav1.Object` (so `meta.Accessor` returns it and `nil`): its
`GetAnnotations()` answers a map (`nil`, or one the caller then owns), an empty map takes the place
of `nil`, the key `k8s.io/initial-events-end` is set to `"true"`, the map is passed to
`SetAnnotations`; the result is `nil`. The object's two methods are the caller's contract: `P`
before, `R` (besides the map) between the calls, `Q` after. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.Assumptions]

/-- See the file header. -/
abbrev storage.AnnotateInitialEventsEndBookmark.spec : Prop :=
  ∀ (ii : GoInterfaceOk) (P R Q : IProp GF),
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ P ∗
      (∀ Ψ : val → IProp GF, P -∗
        ▷ (∀ m : GoMap, R -∗ (⌜m = map.nil⌝ ∨ ∃ M : GMap GoString GoString, ownMap m (DFrac.own 1) M) -∗
          Ψ #m) -∗
        WP (App (Val #(methods ii.ty go!"GetAnnotations" ii.v)) (Val #())) {{ Ψ }}) ∗
      (∀ (m : GoMap) (M : GMap GoString GoString) (Ψ : val → IProp GF), R -∗
        ownMap m (DFrac.own 1) M -∗ ⌜M !! go!"k8s.io/initial-events-end" = some go!"true"⌝ -∗
        ▷ (Q -∗ Ψ #()) -∗
        WP (App (Val #(methods ii.ty go!"SetAnnotations" ii.v)) (Val #m)) {{ Ψ }}) }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.AnnotateInitialEventsEndBookmark))
      (Val #(GoInterface.ok ii)))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ Q }}

end spec

end EtcdGrove
end Perennial
