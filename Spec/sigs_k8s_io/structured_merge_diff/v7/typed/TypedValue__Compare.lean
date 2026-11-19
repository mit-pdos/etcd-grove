/-
`TypedValue.Compare(rhs)` (value receiver): what changed from the receiver to `rhs`, both of one
schema and one type: the paths removed, modified and added (`compare`), as a fresh `Comparison`
(`isComparison`: its three sets). No error in the scope.

Premise (a temporary limitation, local: `fieldpath.Set.Insert` takes a size bound on the set it
inserts into, `typedSizeMax`): the two values together have fewer than `typedSizeMax` nodes
(each changed path is a node of one side: `cmpO_card.law`). Go's memory makes it true of every
value; GooseLang's does not.

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
abbrev typed.TypedValue.Compare.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (q sc : Loc) (S : Schema) (t : TypeRef) (l r : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVv tv sc S t l ∗ isTV q sc S t r ∗ ⌜l.size + r.size < typedSizeMax⌝ }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"Compare")) (Val #q))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜err = interface.nil⌝ ∗ isComparison c (compare S t l r) }}

end spec

end smd
end EtcdGrove
end Perennial
