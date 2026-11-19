/-
`value.EqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `EqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.EqualsUsingBody
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
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
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

theorem value.EqualsUsing.wp_proofBody
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
    (h_valueUnstructured_IsString_ptr : value.valueUnstructured.IsString_ptr.spec (GF := GF)) :
    value.EqualsUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.EqualsUsing.specI
  iintro %al %a %b %dq1 %dq2 %x %y
  wp_start as ⟨Ha, Hx, Hy⟩
  iunfold value.EqualsUsingRec.specI at IH
  icases IH with ⟨-, -, #HLE, #HLEP, #HME⟩
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
  · obtain ⟨nx, rfl⟩ := ValuePure.isIntB_true HxIsInt
    wp_apply h_valueUnstructured_IsInt_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsInt⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isIntB] at HyIsInt
    obtain ⟨ny, rfl⟩ := ValuePure.isIntB_true HyIsInt
    wp_apply h_valueUnstructured_AsInt_ptr p dq1 nx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsInt_ptr q dq2 ny $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    iapply HΦ; iframe; ipureintro
    simp
  wp_apply h_valueUnstructured_IsInt_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsInt⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsInt] at HxIsInt; cases HxIsInt
  wp_apply h_valueUnstructured_IsString_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsString⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨sx, rfl⟩ := ValuePure.isStrB_true HxIsString
    wp_apply h_valueUnstructured_IsString_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsString⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isStrB] at HyIsString
    obtain ⟨sy, rfl⟩ := ValuePure.isStrB_true HyIsString
    wp_apply h_valueUnstructured_AsString_ptr p dq1 sx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsString_ptr q dq2 sy $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    iapply HΦ; iframe; ipureintro
    simp
  wp_apply h_valueUnstructured_IsString_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsString⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsString] at HxIsString; cases HxIsString
  wp_apply h_valueUnstructured_IsBool_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsBool⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨bx, rfl⟩ := ValuePure.isBoolB_true HxIsBool
    wp_apply h_valueUnstructured_IsBool_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsBool⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isBoolB] at HyIsBool
    obtain ⟨by_, rfl⟩ := ValuePure.isBoolB_true HyIsBool
    wp_apply h_valueUnstructured_AsBool_ptr p dq1 bx $$ [Hx] as %r ⟨Hx, %rfl⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsBool_ptr q dq2 by_ $$ [Hy] as %r ⟨Hy, %rfl⟩
    · iexact Hy
    iapply HΦ; iframe; ipureintro
    simp
  wp_apply h_valueUnstructured_IsBool_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsBool⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsBool] at HxIsBool; cases HxIsBool
  wp_apply h_valueUnstructured_IsList_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsList⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vsx, rfl⟩ := ValuePure.isListB_true HxIsList
    wp_apply h_valueUnstructured_IsList_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsList⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isListB] at HyIsList
    obtain ⟨vsy, rfl⟩ := ValuePure.isListB_true HyIsList
    wp_apply h_valueUnstructured_AsListUsing_ptr p dq1 vsx (GoInterface.ok ia) $$ [Hx] as %lv ⟨Hx, #Hlv⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsListUsing_ptr q dq2 vsy (GoInterface.ok ia) $$ [Hy] as %rv ⟨Hy, #Hrv⟩
    · iexact Hy
    ihave %Hlc := isListV_concrete_law_holds lv vsx $$ Hlv
    rcases Hlc with ⟨sl, rfl⟩ | ⟨pl, rfl⟩
    · iunfold value.listUnstructured.EqualsUsing.specI at HLE
      wp_apply HLE $$ %sl %vsx %vsy %(GoInterface.ok ia) %rv [Ha] as %r ⟨Ha, %Hr⟩
      · iframe; isplitr; iexact Hlv; iexact Hrv
      wp_apply HFree $$ %rv [Ha] as Ha
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 rv vsy $$ Hrv; iexact Hf
      wp_apply HFree $$ %(interface.mkOk value.listUnstructured.ty #sl) [Ha] as Ha
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 _ vsx $$ Hlv; iexact Hf
      iapply HΦ; iframe; ipureintro
      simpa using Hr
    · iunfold value.listUnstructured.EqualsUsing_ptr.specI at HLEP
      wp_apply HLEP $$ %pl %vsx %vsy %(GoInterface.ok ia) %rv [Ha] as %r ⟨Ha, %Hr⟩
      · iframe; isplitr; iexact Hlv; iexact Hrv
      wp_apply HFree $$ %rv [Ha] as Ha
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 rv vsy $$ Hrv; iexact Hf
      wp_apply HFree $$ %(interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #pl) [Ha] as Ha
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 _ vsx $$ Hlv; iexact Hf
      iapply HΦ; iframe; ipureintro
      simpa using Hr
  wp_apply h_valueUnstructured_IsList_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsList⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsList] at HxIsList; cases HxIsList
  wp_apply h_valueUnstructured_IsMap_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsMap⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain ⟨vsx, rfl⟩ := ValuePure.isMapB_true HxIsMap
    wp_apply h_valueUnstructured_IsMap_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsMap⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isMapB] at HyIsMap
    obtain ⟨vsy, rfl⟩ := ValuePure.isMapB_true HyIsMap
    wp_apply h_valueUnstructured_AsMapUsing_ptr p dq1 vsx (GoInterface.ok ia) $$ [Hx] as %lv ⟨Hx, #Hlv⟩
    · iexact Hx
    wp_apply h_valueUnstructured_AsMapUsing_ptr q dq2 vsy (GoInterface.ok ia) $$ [Hy] as %rv ⟨Hy, #Hrv⟩
    · iexact Hy
    ihave %Hlc := isMapV_concrete_law_holds lv vsx $$ Hlv
    obtain ⟨gm, rfl⟩ := Hlc
    iunfold value.mapUnstructuredString.EqualsUsing.specI at HME
    wp_apply HME $$ %gm %vsx %vsy %(GoInterface.ok ia) %rv [Ha] as %r ⟨Ha, %Hr⟩
    · iframe; isplitr; iexact Hlv; iexact Hrv
    wp_apply HFree $$ %rv [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 rv vsy $$ Hrv; iexact Hf
    wp_apply HFree $$ %(interface.mkOk value.mapUnstructuredString.ty #gm) [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 _ vsx $$ Hlv; iexact Hf
    iapply HΦ; iframe; ipureintro
    simpa using Hr
  wp_apply h_valueUnstructured_IsMap_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsMap⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsMap] at HxIsMap; cases HxIsMap
  wp_apply h_valueUnstructured_IsNull_ptr p dq1 x $$ [Hx] as %r ⟨Hx, %HxIsNull⟩
  · iexact Hx
  cases r <;> wp_auto
  rotate_left
  · obtain rfl := ValuePure.isNullB_true HxIsNull
    wp_apply h_valueUnstructured_IsNull_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsNull⟩
    · iexact Hy
    cases r <;> wp_auto
    · iapply HΦ; iframe; ipureintro
      simp only [Bool.false_eq_true, false_iff]
      rintro rfl
      simp [UVal.isNullB] at HyIsNull
    obtain rfl := ValuePure.isNullB_true HyIsNull
    iapply HΦ; iframe; ipureintro
    simp
  wp_apply h_valueUnstructured_IsNull_ptr q dq2 y $$ [Hy] as %r ⟨Hy, %HyIsNull⟩
  · iexact Hy
  cases r <;> wp_auto
  rotate_left
  · iapply HΦ; iframe; ipureintro
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl
    rw [← HyIsNull] at HxIsNull; cases HxIsNull
  exfalso
  cases x <;> simp [UVal.isIntB, UVal.isStrB, UVal.isBoolB, UVal.isListB, UVal.isMapB,
    UVal.isNullB] at HxIsInt HxIsString HxIsBool HxIsList HxIsMap HxIsNull

end proof

end smd
end EtcdGrove
end Perennial
