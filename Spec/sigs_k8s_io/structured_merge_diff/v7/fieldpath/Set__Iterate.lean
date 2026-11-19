/-
`Set.Iterate(f)`: calls `f` once on each path of the set, lending it (the path's slice is reused
by later calls: `f` gets it at some fraction for the call only, and copies it to keep it). The
caller's invariant `I` is indexed by the paths visited so far; each call is on a new path of the
set. What the callers need (`merge.ConflictsFromManagers`: each conflict once) is "each path once";
the margin: SMD's order is the trie's preorder (members before children, each in `PE.compare`'s
order).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`merge.ConflictsFromManagers`).
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
abbrev fieldpath.Set.Iterate.spec : Prop :=
  ∀ (p : Loc) (S : PathSet) (f : GoFunc) (I : List Path → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S ∗ I [] ∗
      □ (∀ (done : List Path) (q : Path) (s : GoSlice) (dq : DFrac), ⌜q ∈ S ∧ q ∉ done⌝ -∗
        {{ I done ∗ isPathF s dq q }} (App (Val #f) (Val #s))
        {{ RET #(); I (done ++ [q]) ∗ isPathF s dq q }}) }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Iterate")) (Val #f))
  {{ RET #(); ∃ done : List Path, ⌜done.Nodup ∧ FSet.ofList done = S⌝ ∗ I done }}

end spec

end smd
end EtcdGrove
end Perennial
