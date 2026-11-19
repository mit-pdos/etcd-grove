/-
`PathElementValueMap.Get(pe)`: `(m[pe], true)`, or `(nil, false)` when absent (the stored
`interface{}` asserted back to `value.Value`: never fails, `ownPEVMapV` keeps `isValuePtr`).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s walkers).
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
abbrev fieldpath.PathElementValueMap.Get.spec : Prop :=
  ∀ (l : Loc) (M : PEMap value.Value) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownPEVMap l M ∗ isPE e pe }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap.ty @!! go!"Get")) (Val #e))
  {{ (x : value.Value) (ok : Bool), RET (PairV #x #ok); ownPEVMap l M ∗
      ⌜match M pe with
       | some y => x = y ∧ ok = true
       | none => x = interface.nil ∧ ok = false⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
