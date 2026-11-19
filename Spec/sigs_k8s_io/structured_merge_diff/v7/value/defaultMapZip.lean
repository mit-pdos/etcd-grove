/-
`value.defaultMapZip(a, lhs, rhs, order, fn)` (internal: every `Map.ZipUsing`): as
`MapZipUsing`.

Internal to `value` (PRINCIPLES, "Scope": may mirror its code).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.defaultMapZip.spec : Prop :=
  ∀ (al : value.Allocator) (lm rm : value.Map) (ol or_ : Option (List (GoString × UVal)))
    (order : w64) (fn : GoFunc) (I : List GoString → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isMapO lm ol ∗ isMapO rm or_ ∗ ⌜zipOrderOk order⌝ ∗
      zipFnOk al (order = W64 1) fn ol or_ I Q ∗ I [] }}
    (App (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.defaultMapZip)) (Val #al)) (Val #lm)) (Val #rm)) (Val #order)) (Val #fn))
  {{ (b : Bool), RET #b; isAlloc al ∗ mapIterPost (order = W64 1) (zipKeys ol or_) I Q b }}

end spec

end smd
end EtcdGrove
end Perennial
