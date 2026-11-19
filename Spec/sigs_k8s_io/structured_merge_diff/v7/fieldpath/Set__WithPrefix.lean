/-
`Set.WithPrefix(pe)`: the paths below `pe`, without it (the child set itself, shared, or a fresh
empty set when there is none).

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
abbrev fieldpath.Set.WithPrefix.spec : Prop :=
  ∀ (p : Loc) (S : PathSet) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S ∗ isPE e pe }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"WithPrefix")) (Val #e))
  {{ (r : Loc), RET #r; isSet r (S.under pe) }}

end spec

end smd
end EtcdGrove
end Perennial
