/-
`typed.setItemToPathElement(child)` (internal): the path element of an item of an associative list
without keys (a set): not reached in the scope (`Schema.WF` has no sets). Stated as the code is on
the error side: no error exactly for a scalar item (a `bool`, an `int64`, a `string`).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

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
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.setItemToPathElement.spec : Prop :=
  ∀ (child : value.Value) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isValF child dq x }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.setItemToPathElement)) (Val #child))
  {{ (pe : fieldpath.PathElement) (err : GoInterface), RET (PairV #pe #err); isValF child dq x ∗
      ⌜err = interface.nil ↔ (UVal.isBoolB x = true ∨ UVal.isIntB x = true ∨ UVal.isStrB x = true)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
