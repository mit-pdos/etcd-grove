/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/getPodsLabelSet.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.getPodsLabelSet
public import Proof.k8s_io.kubernetes.pkg.controller.PodLens2

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

theorem getPodsLabelSet.wp_proof : getPodsLabelSet.spec (GF := GF) (hG := hG) := by
  intro tp dq t
  wp_start as Ht
  icases tmplAt_labels tp dq t $$ Ht with ⟨%m, Hm, Hmd, Hback⟩
  wp_auto
  rw [go.make1_underlying, (go.is_underlying :
    underlying k8s_io.apimachinery.pkg.labels.Set'.ty = _)]
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %c Hc
  cases hlab : t.ObjectMeta'.Labels' with
  | none =>
    -- a `nil` map: the loop does nothing
    ihave %hm := ownMapD_none m _ none rfl $$ Hmd
    subst hm
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    wp_call
    wp_auto
    iapply HΦ
    simp only [Option.getD_none]
    iframe Hc
    iapply Hback $$ Hm
    iunfold ownMapD
    ipureintro; rfl
  | some M =>
    ihave Hmd := (ownMapD_some m _ (some M) M rfl).1 $$ Hmd
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (x y : GoString)
        (mv : GMap GoString GoString),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hmv" ∷ ⌜∀ k, mv !! k = if k ∈ keys.take i.toNat then M !! k else none⌝ ∗
        "k" ∷ k_ptr ↦ x ∗
        "v" ∷ v_ptr ↦ y ∗
        "desiredLabels" ∷ desiredLabels_ptr ↦ c ∗
        "Hc" ∷ c ↦$ mv)) $$ Hmd
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [k v desiredLabels Hc]
    · iexists _, _, ∅
      simp only [named]
      iframe
      ipureintro
      refine ⟨Int.le_refl _, fun k => ?_⟩
      simp
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_mapInsert $$ Hc as Hc
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, vv, _
      simp only [named]
      iframe
      ipureintro
      refine ⟨by omega, fun k => ?_⟩
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      rw [Htake, GMap.lookup_insert_eq_iff]
      by_cases hk : key = k
      · subst hk; simp [Hvv]
      · simp only [hk, ↓reduceIte]; rw [Hmv]
        simp [List.mem_append, Ne.symm hk]
    iintro HP Hmd
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
    have Hmv' : mv = M := by
      apply GMap.map_eq; intro k
      rw [Hmv k]
      by_cases hk : k ∈ keys
      · simp only [hk, ↓reduceIte]
      · simp only [hk, ↓reduceIte]
        have := mt (Hkset k).mpr hk
        cases h : M !! k <;> simp_all
    subst Hmv'
    wp_auto
    iapply HΦ
    simp only [Option.getD_some]
    iframe Hc
    iapply Hback $$ Hm
    iapply (ownMapD_some m _ (some mv) mv rfl).2
    iexact Hmd

end proof

end dsctl
end EtcdGrove
end Perennial
