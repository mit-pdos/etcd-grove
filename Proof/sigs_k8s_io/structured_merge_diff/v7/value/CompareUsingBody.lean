/-
`value.CompareUsing`: a member of the recursion cluster `value.CompareUsingRec` (`CompareUsingRec.lean`); its proof is the
projection of the cluster's (its body is `CompareUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsListUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsString_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsBool_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsFloat_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsInt_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsList_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsNull_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsString_ptr
public import Perennial.Spec.strings.Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.BoolCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FloatCompare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.IntCompare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCompare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsRec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

/-- A comparison of values of different kinds (or a contradiction among the kind tests). -/
local macro "cmp_kind" : tactic => `(tactic| first
  | (exfalso; simp [UVal.isIntB, UVal.isStrB, UVal.isBoolB, UVal.isListB, UVal.isMapB, UVal.isNullB] at *; done)
  | (rw [ValueCompare.compare_tag (by simp [ValueCompare.tag])]; simp [ValueCompare.tag]; try decide))

theorem value.CompareUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_valueUnstructured_AsBool_ptr : value.valueUnstructured.AsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_AsFloat_ptr : value.valueUnstructured.AsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_AsInt_ptr : value.valueUnstructured.AsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_AsListUsing_ptr : value.valueUnstructured.AsListUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_AsString_ptr : value.valueUnstructured.AsString_ptr.spec (GF := GF))
    (h_valueUnstructured_IsBool_ptr : value.valueUnstructured.IsBool_ptr.spec (GF := GF))
    (h_valueUnstructured_IsFloat_ptr : value.valueUnstructured.IsFloat_ptr.spec (GF := GF))
    (h_valueUnstructured_IsInt_ptr : value.valueUnstructured.IsInt_ptr.spec (GF := GF))
    (h_valueUnstructured_IsList_ptr : value.valueUnstructured.IsList_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_IsNull_ptr : value.valueUnstructured.IsNull_ptr.spec (GF := GF))
    (h_valueUnstructured_IsString_ptr : value.valueUnstructured.IsString_ptr.spec (GF := GF))
    (h_strings_Compare : _root_.Perennial.strings.Compare.spec (GF := GF))
    (h_BoolCompare : value.BoolCompare.spec (GF := GF))
    (h_FloatCompare : value.FloatCompare.spec (GF := GF))
    (h_IntCompare : value.IntCompare.spec (GF := GF)) :
    value.CompareUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.CompareUsing.specI
  iintro %al %a %b %dq1 %dq2 %x %y
  wp_start as ⟨Ha, Hx, Hy, %Hok⟩
  iunfold value.CompareUsingRec.specI at IH
  icases IH with ⟨-, #HLC, #HMC⟩
  iunfold value.ListCompareUsing.specI at HLC
  iunfold value.MapCompareUsing.specI at HMC
  ihave %Hcx := isValF_concrete_law_holds a dq1 x $$ Hx
  ihave %Hcy := isValF_concrete_law_holds b dq2 y $$ Hy
  obtain ⟨p, rfl⟩ := Hcx
  obtain ⟨q, rfl⟩ := Hcy
  ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_valueUnstructured_IsFloat_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %rfl⟩
  · iexact Hx
  wp_apply h_valueUnstructured_IsFloat_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %rfl⟩
  · iexact Hy
  wp_apply h_valueUnstructured_IsInt_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsInt⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vx, rfl⟩ := ValuePure.isIntB_true HxIsInt
    wp_apply h_valueUnstructured_IsInt_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsInt⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain ⟨vy, rfl⟩ := ValuePure.isIntB_true HyIsInt
    wp_apply h_valueUnstructured_AsInt_ptr p dq1 vx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsInt_ptr q dq2 vy $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    wp_apply h_IntCompare _ _ as %c %Hc
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_int]; exact Hc
  wp_apply h_valueUnstructured_IsInt_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsInt⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain ⟨_, rfl⟩ := ValuePure.isIntB_true HyIsInt
    cases x <;> cmp_kind
  wp_apply h_valueUnstructured_IsString_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsString⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vx, rfl⟩ := ValuePure.isStrB_true HxIsString
    wp_apply h_valueUnstructured_IsString_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsString⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain ⟨vy, rfl⟩ := ValuePure.isStrB_true HyIsString
    wp_apply h_valueUnstructured_AsString_ptr p dq1 vx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsString_ptr q dq2 vy $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    wp_apply h_strings_Compare
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_str]; exact ValuePure.compareResult_gs _ _
  wp_apply h_valueUnstructured_IsString_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsString⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain ⟨_, rfl⟩ := ValuePure.isStrB_true HyIsString
    cases x <;> cmp_kind
  wp_apply h_valueUnstructured_IsBool_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsBool⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vx, rfl⟩ := ValuePure.isBoolB_true HxIsBool
    wp_apply h_valueUnstructured_IsBool_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsBool⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain ⟨vy, rfl⟩ := ValuePure.isBoolB_true HyIsBool
    wp_apply h_valueUnstructured_AsBool_ptr p dq1 vx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsBool_ptr q dq2 vy $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    wp_apply h_BoolCompare _ _ as %c %Hc
    iapply HΦ; iframe; ipureintro
    rw [ValueCompare.compare_bool]; exact Hc
  wp_apply h_valueUnstructured_IsBool_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsBool⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain ⟨_, rfl⟩ := ValuePure.isBoolB_true HyIsBool
    cases x <;> cmp_kind
  wp_apply h_valueUnstructured_IsList_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsList⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vx, rfl⟩ := ValuePure.isListB_true HxIsList
    wp_apply h_valueUnstructured_IsList_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsList⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain ⟨vy, rfl⟩ := ValuePure.isListB_true HyIsList
    wp_apply h_valueUnstructured_AsListUsing_ptr p dq1 vx (GoInterface.ok ia) $$ [Hx] as %lv ⟨Hx, #Hlv⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsListUsing_ptr q dq2 vy (GoInterface.ok ia) $$ [Hy] as %rv ⟨Hy, #Hrv⟩
    · iexact Hy
    wp_apply HLC $$ %(GoInterface.ok ia) %lv %rv %vx %vy [Ha] as %c ⟨Ha, %Hc⟩
    · iframe; isplitr; iexact Hlv; isplitr; iexact Hrv; ipureintro; exact Hok
    wp_apply HFree $$ %rv [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 rv vy $$ Hrv; iexact Hf
    wp_apply HFree $$ %lv [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 lv vx $$ Hlv; iexact Hf
    iapply HΦ; iframe; ipureintro
    exact Hc
  wp_apply h_valueUnstructured_IsList_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsList⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain ⟨_, rfl⟩ := ValuePure.isListB_true HyIsList
    cases x <;> cmp_kind
  wp_apply h_valueUnstructured_IsMap_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsMap⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vx, rfl⟩ := ValuePure.isMapB_true HxIsMap
    wp_apply h_valueUnstructured_IsMap_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsMap⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain ⟨vy, rfl⟩ := ValuePure.isMapB_true HyIsMap
    wp_apply h_valueUnstructured_AsMapUsing_ptr p dq1 vx (GoInterface.ok ia) $$ [Hx] as %lv ⟨Hx, #Hlv⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsMapUsing_ptr q dq2 vy (GoInterface.ok ia) $$ [Hy] as %rv ⟨Hy, #Hrv⟩
    · iexact Hy
    wp_apply HMC $$ %(GoInterface.ok ia) %lv %rv %(some vx) %(some vy) [Ha] as %c ⟨Ha, %Hc⟩
    · iframe; simp only [isMapO]; isplitr; iexact Hlv; isplitr; iexact Hrv
      ipureintro; simpa [kvsOrEmpty] using Hok
    wp_apply HFree $$ %rv [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 rv vy $$ Hrv; iexact Hf
    wp_apply HFree $$ %lv [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 lv vx $$ Hlv; iexact Hf
    iapply HΦ; iframe; ipureintro
    simpa [kvsOrEmpty] using Hc
  wp_apply h_valueUnstructured_IsMap_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsMap⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain ⟨_, rfl⟩ := ValuePure.isMapB_true HyIsMap
    cases x <;> cmp_kind
  wp_apply h_valueUnstructured_IsNull_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsNull⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain rfl := ValuePure.isNullB_true HxIsNull
    wp_apply h_valueUnstructured_IsNull_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsNull⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      cases y <;> cmp_kind
    obtain rfl := ValuePure.isNullB_true HyIsNull
    iapply HΦ; iframe; ipureintro
    rfl
  wp_apply h_valueUnstructured_IsNull_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsNull⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    obtain rfl := ValuePure.isNullB_true HyIsNull
    cases x <;> cmp_kind
  exfalso
  cases x <;> simp [UVal.isIntB, UVal.isStrB, UVal.isBoolB, UVal.isListB, UVal.isMapB,
    UVal.isNullB] at HxIsInt HxIsString HxIsBool HxIsList HxIsMap HxIsNull

end proof

end smd
end EtcdGrove
end Perennial
