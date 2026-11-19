/-
`Set.Has(p)`: whether the path `p` is in the set (`false` for the empty path).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s removing walker).
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
abbrev fieldpath.Set.Has.spec : Prop :=
  ∀ (p : Loc) (S : PathSet) (s : GoSlice) (dq : DFrac) (q : Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S ∗ isPathF s dq q }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Has")) (Val #s))
  {{ (r : Bool), RET #r; isPathF s dq q ∗ ⌜r = true ↔ q ∈ S⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
