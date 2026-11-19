/-
`SetNodeMap.Get(pe)`: the child set at `pe` (the paths below it), or `(nil, false)` when there is
none (binary search). A client reaching a set's children (`typed`'s reconciliation) holds them
through `isSet_split`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s reconciliation reads `element.Children`); `Set.Has`, `Set.WithPrefix`.
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
abbrev fieldpath.SetNodeMap.Get.spec : Prop :=
  ∀ (l : Loc) (D : PathSet) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isPE e pe }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Get")) (Val #e))
  {{ (q : Loc) (ok : Bool), RET (PairV #q #ok);
      ⌜ok = true ↔ pe ∈ D.heads⌝ ∗ (if ok then isSet q (D.under pe) else ⌜q = null⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
