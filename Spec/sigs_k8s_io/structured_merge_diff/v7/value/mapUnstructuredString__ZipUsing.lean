/-
`mapUnstructuredString.ZipUsing(a, other, order, fn)`: `MapZipUsing` with this map on the
left (`other` may be nil).

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
abbrev value.mapUnstructuredString.ZipUsing.spec : Prop :=
  ∀ (m : GoMap) (kvs : List (GoString × UVal)) (al : value.Allocator) (o : value.Map)
    (or_ : Option (List (GoString × UVal))) (order : w64) (fn : GoFunc)
    (I : List GoString → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV (interface.mkOk value.mapUnstructuredString.ty #m) kvs ∗ isMapO o or_ ∗ isAlloc al ∗ ⌜zipOrderOk order⌝ ∗
      zipFnOk al (order = W64 1) fn (some kvs) or_ I Q ∗ I [] }}
    (App (App (App (App (Val (m @!! value.mapUnstructuredString.ty @!! go!"ZipUsing")) (Val #al)) (Val #o)) (Val #order)) (Val #fn))
  {{ (r : Bool), RET #r; isAlloc al ∗ mapIterPost (order = W64 1) (zipKeys (some kvs) or_) I Q r }}

end spec

end smd
end EtcdGrove
end Perennial
