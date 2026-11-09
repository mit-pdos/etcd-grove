/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/growSlice.lean`: the loop keeps `max ≥ cap`; the
capacity asked of `MakeSlice` is then above the length and at most `mx`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.growSlice
public import Spec.reflect.Value__Cap
public import Spec.reflect.Value__Len
public import Spec.reflect.Value__Type
public import Spec.reflect.Value__Set

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver reflectM

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem growSlice.wp_proof
    (wp_Cap : reflect.Value.Cap.spec (GF := GF) (hG := hG))
    (wp_Len : reflect.Value.Len.spec (GF := GF) (hG := hG))
    (wp_Type : reflect.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Set : reflect.Value.Set.spec (GF := GF) (hG := hG)) :
    growSlice.spec (GF := GF) (hG := hG) := by
  intro Obj S L vp v p s os mx szs zs hmx
  wp_start as ⟨#Hlc, %hv, Hp, Hit, #Hz⟩
  ihave #Pr : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  unfold listContractOk'
  icases Hlc with ⟨-, #HM0, #HMn, -⟩
  icases persistent_entails_left (L.itemsAt_wf s os) $$ Hit with ⟨Hit, %Hwf⟩
  icases persistent_entails_left (L.itemsAt_len s os) $$ Hit with ⟨Hit, %Hlen⟩
  wp_auto
  wp_apply (wp_Cap v_ptr _ _ v S.objTy p s) $$ [$v $Hp] as ⟨v, Hp⟩
  · ipureintro; exact hv
  ihave %Hzl := ownSlice_len szs DFrac.discard zs $$ Hz
  -- the loop keeps `max ≥ cap`
  ihave HV : (∃ (j mv sz : w64), "i" ∷ i_ptr ↦ j ∗ "max" ∷ max_ptr ↦ mv ∗ "size" ∷ size_ptr ↦ sz ∗
      "%Hj" ∷ ⌜sint.Z s.cap ≤ sint.Z mv ∧ 0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z szs.len⌝ : IProp GF)
      $$ [i max size]
  · iexists W64 0, s.cap, zero_val w64
    simp only [named]
    iframe
    ipureintro; refine ⟨Int.le_refl _, by decide, ?_⟩; word
  wp_for HV
  wp_if_destruct
  · have hlt : sint.Z j < sint.Z szs.len := by
      exact Hif
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z szs.len := ⟨Hj.2.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    list_elem zs (sint.nat j) as z
    wp_apply wp_load_slice_index szs (sint.Z j) zs _ z hb.1 $$ [$Hz] as -
    · ipureintro; exact Hz_lookup
    wp_if_destruct
    · wp_for_post
      iframe
      iexists j + W64 1, z, z
      simp only [named]
      iframe
      ipureintro; refine ⟨?_, ?_, ?_⟩ <;> word
    · wp_for_post
      iframe
      iexists j + W64 1, mv, z
      simp only [named]
      iframe
      ipureintro; refine ⟨Hj.1, ?_, ?_⟩ <;> word
  · by_cases hz : szs.len = W64 0
    case' pos =>
      rw [decide_eq_true hz]
      (try wp_auto)
    case' neg =>
      rw [decide_eq_false hz]
      (try wp_auto)
      by_cases hm : sint.Z mx < sint.Z mv
      case' pos =>
        rw [decide_eq_true hm]
        (try wp_auto)
      case' neg =>
        rw [decide_eq_false hm]
        (try wp_auto)
    all_goals
      wp_if_destruct
      · iapply HΦ
        iexists s
        iframe
      · wp_apply (wp_Len v_ptr _ _ v S.objTy p s) $$ [$v $Hp] as ⟨v, Hp⟩
        · ipureintro; exact hv
        wp_if_destruct
        · -- items: a new slice of capacity `max`, the items copied
          wp_apply (wp_Type v_ptr _ v _ _) $$ [$v] as %rt ⟨v, %hrt⟩
          · ipureintro; exact hv
          wp_apply (wp_Len v_ptr _ _ v S.objTy p s) $$ [$v $Hp] as ⟨v, Hp⟩
          · ipureintro; exact hv
          wp_bind
          ihave Hmk := HMn $$ %rt %s.len %_ %os
          iapply Hmk
          · ipureintro
            refine ⟨hrt, ?_, ?_, ?_, ?_⟩ <;> word
          inext
          iintro %w %s' %hw Hcopy
          (try wp_auto)
          wp_bind
          iapply Hcopy $$ %v %p %(DFrac.own 1) %s %_ %hv Hp Hit
          inext
          iintro %r Hp Hit'
          (try wp_auto)
          wp_apply (wp_Set v_ptr _ v w (go.GoType.SliceType S.objTy) p GoSlice s s') $$ [$v $Hp]
            as ⟨v, Hp⟩
          · ipureintro; exact ⟨hv, Or.inr ⟨S.objTy, s', rfl, hw, HEq.rfl⟩⟩
          iapply HΦ
          iexists s'
          iframe
        · -- no items: a new empty slice of capacity `max`
          have hos : os = [] := List.eq_nil_of_length_eq_zero (by rw [← Hlen]; word)
          subst hos
          wp_apply (wp_Type v_ptr _ v _ _) $$ [$v] as %rt ⟨v, %hrt⟩
          · ipureintro; exact hv
          (try wp_auto)
          wp_bind
          ihave Hmk := HM0 $$ %rt %_
          iapply Hmk
          · ipureintro
            refine ⟨hrt, ?_, ?_⟩ <;> word
          inext
          iintro %w %s' %hw Hit'
          (try wp_auto)
          wp_apply (wp_Set v_ptr _ v w (go.GoType.SliceType S.objTy) p GoSlice s s') $$ [$v $Hp]
            as ⟨v, Hp⟩
          · ipureintro; exact ⟨hv, Or.inr ⟨S.objTy, s', rfl, hw, HEq.rfl⟩⟩
          iapply HΦ
          iexists s'
          iframe

end proof

end k8s
end EtcdGrove
end Perennial
