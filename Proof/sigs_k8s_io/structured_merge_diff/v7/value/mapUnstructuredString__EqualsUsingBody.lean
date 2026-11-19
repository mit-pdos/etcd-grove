/-
`value.mapUnstructuredString.EqualsUsing`: a member of the recursion cluster `value.EqualsUsingRec` (`EqualsUsingRec.lean`); its proof is the
projection of the cluster's (its body is `mapUnstructuredString__EqualsUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__EqualsUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse
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

theorem value.mapUnstructuredString.EqualsUsing.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_freelistAllocator_allocValueUnstructured : value.freelistAllocator.allocValueUnstructured.spec (GF := GF))
    (h_mapUnstructuredString_IterateUsing : value.mapUnstructuredString.IterateUsing.spec (GF := GF))
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.mapUnstructuredString.EqualsUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.mapUnstructuredString.EqualsUsing.specI
  iintro %m %kvs %kvs' %al %o
  wp_start as ⟨#Hm, #Ho, Ha⟩
  iunfold value.EqualsUsingRec.specI at IH
  icases IH with ⟨#HEq, -, -, -, -⟩
  iunfold value.EqualsUsing.specI at HEq
  ihave %Hco := isMapV_concrete_law_holds o kvs' $$ Ho
  obtain ⟨gm', rfl⟩ := Hco
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_method_call
  wp_auto
  wp_apply h_mapUnstructuredString_Length m kvs as %n1 %Hn1
  · iexact Hm
  wp_apply h_mapUnstructuredString_Length gm' kvs' as %n2 %Hn2
  · iexact Ho
  wp_if_destruct
  · ihave ⟨Ha, %ia, %Hia, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
    · iframe; iexact Hpkg
    ihave ⟨Ha, %ia', %Hia', #HAlloc⟩ := isAlloc_allocV h_heapAllocator_allocValueUnstructured
      h_freelistAllocator_allocValueUnstructured al $$ [Ha]
    · iframe; iexact Hpkg
    subst Hia
    cases Hia'
    ihave #Hmi := isMapV_val $$ Hm
    icases isIface_map_val $$ Hmi with ⟨%M, #HM, %HkM, #HLM⟩
    ihave #Hoi := isMapV_val $$ Ho
    icases isIface_map_val $$ Hoi with ⟨%M', -, %HkM', -⟩
    by_cases hz : n1 = W64 0
    · simp only [hz, decide_true]
      wp_auto
      iapply HΦ; iframe; ipureintro
      have h1 : kvs = [] := List.eq_nil_of_length_eq_zero (by subst hz; word)
      have h2 : kvs' = [] := List.eq_nil_of_length_eq_zero (by subst hz Hif; word)
      simp [h1, h2]
    simp only [hz, decide_false]
    wp_auto
    wp_apply HAlloc $$ [Ha] as %vv ⟨Ha, Hvv⟩
    · iexact Ha
    ipersist m
    ipersist a
    ipersist vv
    wp_func_lits
    wp_apply h_mapUnstructuredString_IterateUsing gm' kvs' (GoInterface.ok ia) _
      (fun done => iprop(wrapperOwn vv ∗ ⌜∀ k ∈ done, lookupKV k kvs = lookupKV k kvs'⌝))
      (iprop(wrapperOwn vv ∗ ⌜kvs ≠ kvs'⌝)) $$ [Ha Hvv] as %r ⟨Ha, Hr⟩
    · iframe
      isplitr
      · iexact Ho
      isplitr
      · iunfold iterUFnOk
        imodintro
        iintro %done %k %x' %v %Hst %Φ' !> ⟨Ha, ⟨Hvv, %Hdone⟩, Hv⟩ HΦ'
        simp only [← recv_eq_func_mk]
        wp_call
        wp_auto
        wp_apply wp_map_lookup2 go.string (go.InterfaceType []) m M k DFrac.discard as -
        · iexact HM
        cases hl : lookupKV k kvs with
        | none =>
          have hM : M !! k = none := by
            have := HkM.2 k; rw [hl] at this; simpa using this
          simp only [hM, Option.isSome_none, Bool.false_eq_true, decide_false]
          wp_auto
          iapply HΦ'
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          ipureintro
          intro he; subst he
          rw [hl] at Hst; cases Hst.1
        | some x =>
          ihave ⟨%i, %Hmi, #Hxi⟩ := isIfaceM_lookup M k x kvs hl $$ HLM
          simp only [Hmi, Option.isSome_some, decide_true, Option.getD_some]
          wp_auto
          wp_apply h_valueUnstructured_reuse vv i x $$ [Hvv] as %w ⟨%rfl, Hw⟩
          · iframe; iexact Hxi
          wp_apply HEq $$ %(GoInterface.ok ia) %_ %v %(DFrac.own 1) %(DFrac.own 1) %x %x' [Ha Hw Hv]
            as %r ⟨Ha, Hw, Hv, %Hr⟩
          · iframe
          ihave Hvv := isValF_wrapperOwn $$ Hw
          iapply HΦ'
          cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> iframe
          · ipureintro
            intro he; subst he
            rw [hl] at Hst
            exact absurd (Hr.2 (Option.some_inj.1 Hst.1)) (by simp)
          · ipureintro
            intro k' hk'
            rcases List.mem_append.1 hk' with h | h
            · exact Hdone k' h
            · simp at h; subst h
              rw [hl, Hst.1, Hr.1 rfl]
      · ipureintro; simp
    iunfold mapIterPost at Hr
    cases r
    · isimp at Hr
      icases Hr with ⟨Hvv, %Hne⟩
      wp_apply HFree $$ %(interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #vv) [Ha Hvv] as Ha
      · iframe; iapply wrapperOwn_freeable; iexact Hvv
      iapply HΦ; iframe; ipureintro
      simp [Hne]
    · isimp at Hr
      icases Hr with ⟨%done, %Hperm, Hvv, %Hd⟩
      wp_apply HFree $$ %(interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #vv) [Ha Hvv] as Ha
      · iframe; iapply wrapperOwn_freeable; iexact Hvv
      iapply HΦ; iframe; ipureintro
      simp only [true_iff]
      simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at Hperm
      apply ValuePure.kvs_eq_of_lookups kvs kvs' HkM.1 HkM'.1 (by subst Hif; omega)
      intro k hk
      exact Hd k (Hperm.mem_iff.2 hk)
  · iapply HΦ; iframe; ipureintro
    constructor
    · intro h; cases h
    · intro h; subst h; exact absurd (by apply BitVec.eq_of_toInt_eq; omega) Hif

end proof

end smd
end EtcdGrove
end Perennial
