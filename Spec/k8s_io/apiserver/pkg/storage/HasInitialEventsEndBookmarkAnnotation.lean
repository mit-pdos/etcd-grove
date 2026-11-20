/-
`storage.HasInitialEventsEndBookmarkAnnotation(obj)` (`k8s.io/apiserver/pkg/storage/util.go:108`;
translated with its body; k8s 7g step 5, the checker's `splitInitialEvents` and
`validateBookmarks`) of an object whose dynamic type is a `metav1.Object` (so `meta.Accessor`
returns it and `nil`): whether its `GetAnnotations()` maps `k8s.io/initial-events-end` to `"true"`,
and `nil`. The object's method is the caller's contract: `P` before and after; it answers `nil`
(then the result `b` is `false`) or a map it shares with the caller, whose entry decides `b`.
Lean-first (no Rocq counterpart).
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
abbrev storage.HasInitialEventsEndBookmarkAnnotation.spec : Prop :=
  ∀ (ii : GoInterfaceOk) (P : IProp GF) (b : Bool),
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.apis.«meta».v1.Object.ty = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage ∗ P ∗
      (∀ Ψ : val → IProp GF, P -∗
        ▷ (∀ m : GoMap, P -∗
          (⌜m = map.nil ∧ b = false⌝ ∨ ∃ (M : GMap GoString GoString) (dq : DFrac),
            ownMap m dq M ∗ ⌜b = decide (M !! go!"k8s.io/initial-events-end" = some go!"true")⌝) -∗
          Ψ #m) -∗
        WP (App (Val #(methods ii.ty go!"GetAnnotations" ii.v)) (Val #())) {{ Ψ }}) }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.HasInitialEventsEndBookmarkAnnotation))
      (Val #(GoInterface.ok ii)))
  {{ RET (PairV #b #GoInterface.nil); P }}

end spec

end EtcdGrove
end Perennial
