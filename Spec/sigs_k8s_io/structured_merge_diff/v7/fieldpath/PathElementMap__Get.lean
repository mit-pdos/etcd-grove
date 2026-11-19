/-
`PathElementMap.Get(pe)`: `(m[pe], true)`, or `(nil, false)` when absent.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s compare and merge walkers).
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
abbrev fieldpath.PathElementMap.Get.spec : Prop :=
  ∀ (l : Loc) (M : PEMap GoInterface) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownPEMap l M ∗ isPE e pe }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap.ty @!! go!"Get")) (Val #e))
  {{ (x : GoInterface) (ok : Bool), RET (PairV #x #ok); ownPEMap l M ∗
      ⌜match M pe with
       | some y => x = y ∧ ok = true
       | none => x = interface.nil ∧ ok = false⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
