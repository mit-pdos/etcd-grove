/-
**`value`'s recursion clusters' specs inside the logic are persistent** (structured-merge-diff
v7.0.0): the member bodies use their Löb hypothesis (`▷ <C>.specI`) more than once. A defs-tier
module (it imports the clusters' specs). Prove phase (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsingRec
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsingRec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

instance EqualsUsingRec_specI_pers : Persistent (value.EqualsUsingRec.specI (GF := GF)) := by
  unfold value.EqualsUsingRec.specI value.EqualsUsing.specI value.ListEqualsUsing.specI
    value.listUnstructured.EqualsUsing.specI value.listUnstructured.EqualsUsing_ptr.specI
    value.mapUnstructuredString.EqualsUsing.specI
  infer_instance

instance CompareUsingRec_specI_pers : Persistent (value.CompareUsingRec.specI (GF := GF)) := by
  unfold value.CompareUsingRec.specI value.CompareUsing.specI value.ListCompareUsing.specI
    value.MapCompareUsing.specI
  infer_instance

end lemmas

end smd
end EtcdGrove
end Perennial
