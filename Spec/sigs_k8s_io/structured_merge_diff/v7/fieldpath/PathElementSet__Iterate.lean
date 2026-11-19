/-
`PathElementSet.Iterate(f)`: calls `f` once on each member. The caller's invariant `I` is indexed
by the members visited so far; each call is on a new member. The margin: SMD visits them in
`PE.compare`'s order (stated only as "each once": no caller needs the order).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s reconciliation iterates a set's members); `Set.iteratePrefix`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

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
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.PathElementSet.Iterate.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (S : FSet PE) (f : GoFunc) (I : List PE → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPESet l dq S ∗ I [] ∗
      □ (∀ (done : List PE) (e : fieldpath.PathElement) (x : PE), ⌜x ∈ S ∧ x ∉ done⌝ -∗
        {{ I done ∗ isPE e x }} (App (Val #f) (Val #e)) {{ RET #(); I (done ++ [x]) }}) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet.ty @!! go!"Iterate")) (Val #f))
  {{ RET #(); isPESet l dq S ∗ ∃ done : List PE, ⌜done.Nodup ∧ FSet.ofList done = S⌝ ∗ I done }}

end spec

end smd
end EtcdGrove
end Perennial
