/-
`mapUnstructuredString.Length()`: the number of entries.

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
abbrev value.mapUnstructuredString.Length.spec : Prop :=
  ∀ (m : GoMap) (kvs : List (GoString × UVal)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV (interface.mkOk value.mapUnstructuredString.ty #m) kvs }}
    (App (Val (m @!! value.mapUnstructuredString.ty @!! go!"Length")) (Val #()))
  {{ (r : w64), RET #r; ⌜r.toInt = kvs.length⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
