/-
`value.mapUnstructuredString.IterateUsing`: proved (Prove step, notes/smd-plan.md). Its callees' specs (and the interface bundles' laws, `Objects.lean`) are its
hypotheses. Lean-first (2026-11-19), Draft.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__IterateUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__allocValueUnstructured
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__reuse
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch

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

theorem value.mapUnstructuredString.IterateUsing.wp_proof
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_heapAllocator_allocValueUnstructured : value.heapAllocator.allocValueUnstructured.spec (GF := GF))
    (h_freelistAllocator_allocValueUnstructured : value.freelistAllocator.allocValueUnstructured.spec (GF := GF))
    (h_valueUnstructured_reuse : value.valueUnstructured.reuse.spec (GF := GF)) :
    value.mapUnstructuredString.IterateUsing.spec (GF := GF) := fun m kvs al fn I Q => by
  wp_start as ⟨Hm, Ha, #Hfn, HI⟩
  ihave #Hi := isMapV_val $$ Hm
  icases isIface_map_val $$ Hi with ⟨%M, #HM, %Hk, #HL⟩
  have hsz := map_size_kvs M kvs Hk.1 Hk.2
  ihave ⟨Ha, %i, %Hai, #HFree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free al $$ [Ha]
  · iframe; iexact Hpkg
  ihave ⟨Ha, %i', %Hai', #HAlloc⟩ := isAlloc_allocV h_heapAllocator_allocValueUnstructured
    h_freelistAllocator_allocValueUnstructured al $$ [Ha]
  · iframe; iexact Hpkg
  subst Hai
  cases Hai'
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply wp_map_len_lt m M DFrac.discard as ⟨-, %Hlt⟩
  · iexact HM
  wp_if_destruct
  · have hk0 : kvs = [] := List.eq_nil_of_length_eq_zero (by word)
    subst hk0
    iapply HΦ; iframe
    simp only [mapIterPost, ↓reduceIte]
    iexists []; iframe; ipureintro; simp [mapIterDone, kvKeys]
  · wp_apply HAlloc $$ [Ha] as %vv ⟨Ha, Hvv⟩
    · iexact Ha
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (j : Int) => iprop(
        ∃ (x : GoInterface) (s : GoString) (b : Bool), "%Hj" ∷ ⌜0 ≤ j⌝ ∗
        "v" ∷ v_ptr ↦ x ∗ "k" ∷ k_ptr ↦ s ∗ "Ha" ∷ isAlloc (.ok i) ∗ "Hvv" ∷ wrapperOwn vv ∗
        "HI" ∷ I (keys.take j.toNat) ∗ "HΦ" ∷ (∀ r, isAlloc (GoInterface.ok i) ∗
          mapIterPost false (kvKeys kvs) I Q r -∗ Φ #r) ∗
        "res0" ∷ «$res0_ptr» ↦ b ∗ "fn" ∷ fn_ptr ↦ fn ∗ "vv" ∷ vv_ptr ↦ vv ∗
        "defer" ∷ defer ↦ func.mk BAnon BAnon
          (Seq (App (Val #(methods i.ty go!"Free" i.v))
              (Val #(interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #vv)))
            (App (Val #(func.mk BAnon BAnon (Val #()))) (Val #())))))
      _ go.string (go.InterfaceType []) m M DFrac.discard $$ [HM]
    · iexact HM
    iintro %keys ⟨%Hkm, %Hklen, %Hknd⟩
    isplitl [v k Ha Hvv HI HΦ «$res0» fn vv defer]
    · iexists _, _, _
      simp only [named, Int.toNat_zero, List.take_zero]
      iframe
      ipureintro; omega
    isplitr
    · imodintro
      iintro %j %key %iv ⟨%Hkey, %Hmv⟩ HP
      iNamed HP
      wp_auto
      have hks : (lookupKV key kvs).isSome = true := by rw [← Hk.2]; simp [Hmv]
      obtain ⟨xv, hxv⟩ := Option.isSome_iff_exists.mp hks
      ihave ⟨%iv', %Hiv', #Hxi⟩ := isIfaceM_lookup M key xv kvs hxv $$ HL
      rw [Hmv] at Hiv'; cases Hiv'
      wp_apply h_valueUnstructured_reuse vv iv xv $$ [Hvv] as %w ⟨%rfl, Hw⟩
      · iframe; iexact Hxi
      have hstep : mapIterStep false (kvKeys kvs) (keys.take j.toNat) key := by
        simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte]
        exact ⟨(ValuePure.lookupKV_isSome_iff key kvs).1 hks,
          ValuePure.nodup_not_mem_take keys Hknd _ _ Hkey⟩
      iunfold iterUFnOk at Hfn
      wp_apply Hfn $$ %(keys.take j.toNat) %key %xv %_ %(And.intro hxv hstep) [Ha HI Hw] as %r ⟨Ha, Hw, Hr⟩
      · iframe
      ihave Hvv := isValF_wrapperOwn $$ Hw
      cases r
      · wp_auto
        iunfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro -
        wp_auto
        wp_apply HFree $$ %(interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #vv) [Ha Hvv] as Ha
        · iframe; iapply wrapperOwn_freeable; iexact Hvv
        iapply HΦ
        iframe
        iunfold mapIterPost
        isimp
        isimp at Hr
        iexact Hr
      · wp_auto
        iunfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists _, _, _
        rw [show (j + 1).toNat = j.toNat + 1 by omega,
          ValuePure.take_succ_of_getElem? keys _ key Hkey]
        isimp at Hr
        iframe
        ipureintro; omega
    · iintro HP Hm'
      iNamed HP
      wp_auto
      wp_apply HFree $$ %(interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #vv) [Ha Hvv] as Ha
      · iframe; iapply wrapperOwn_freeable; iexact Hvv
      iapply HΦ
      iframe
      iunfold mapIterPost
      isimp
      iexists keys
      have htk : List.take (↑M.size : Int).toNat keys = keys := by
        rw [List.take_of_length_le]; omega
      rw [htk]
      iframe
      ipureintro
      simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte]
      apply ValuePure.perm_of_nodup_mem _ _ Hknd (ValuePure.keysSorted_nodup kvs Hk.1)
      intro a
      rw [Hkm, ← ValuePure.lookupKV_isSome_iff, Hk.2]

end proof

end smd
end EtcdGrove
end Perennial
