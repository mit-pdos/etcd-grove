/-
Proof of `Spec/k8s_io/client_go/tools/cache/reconcileReplacement.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.reconcileReplacement
public import Spec.k8s_io.client_go.tools.cache.cache__ListKeys
public import Spec.k8s_io.client_go.tools.cache.cache__GetByKey
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apimachinery.pkg.util.sets.KeySet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem reconcileReplacement.wp_proof
    (wp_ListKeys : cache.ListKeys.spec (GF := GF) (hG := hG))
    (wp_GetByKey : cache.GetByKey.spec (GF := GF) (hG := hG))
    (wp_Insert : sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_Has : sets.Set.Has.spec (GF := GF) (hG := hG)) :
    reconcileReplacement.spec (GF := GF) (hG := hG) := by
  intro lg ca ts γ OK Fam kf kf' KF SW Rw σ nsl dq objs od orp Dl Rl
  wp_start as ⟨#Hca, Hr, #Hsw, HSW, %HRw, Hnsl, #Hkey, HD, HR, #Hod, #Horp⟩
  ihave #Hsets : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hnsl
  iunfold keyOk at Hkey
  (try wp_auto)
  wp_apply (wp_map_make1 (K := GoString) (V := sets.Elem) go.string
    k8s_io.apimachinery.pkg.util.sets.Empty.ty) as %nk Hnk
  (try wp_auto)
  -- the new items' keys
  ihave IH : iprop(∃ (n : w64) (x : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "obj" ∷ obj_ptr ↦ x ∗
      "Hnk" ∷ nk ↦$ sets.insertAll ∅ ((objs.take (sint.nat n)).map KF) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ objs.length⌝) $$ [i obj Hnk]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < objs.length := by word
    obtain ⟨e, He⟩ : ∃ e, objs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z nsl.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index nsl (sint.Z n) objs dq e Hn.1 $$ [Hnsl] as Hnsl
    · iframe; ipureintro; exact He
    (try wp_auto)
    wp_apply Hkey
    · ipureintro; exact List.mem_of_getElem? He
    iintro %k %err %hk
    obtain ⟨rfl, rfl⟩ := hk
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Insert) $$ [$newKeys $Hnk $Hl1] as ⟨newKeys, Hnk, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, e
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
      have := Hn.1; have := Hlt; have := Hlen.1; word
    have h1 : 0 ≤ sint.Z (n + W64 1) := by have := Hn.1; have := Hlt; have := Hlen.1; word
    rw [hn1, List.take_add_one, He]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, sets.insertAll_append]
    iframe
    ipureintro
    exact ⟨h1, by omega⟩
  · have hnl : sint.nat n = objs.length := by word
    rw [hnl, List.take_length]
    (try wp_auto)
    wp_apply (wp_slice_literal (V := GoString))
    isplitr
    · ipureintro; rfl
    iintro %qk ⟨Hqk, -⟩
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := Delta) go.string Delta.ty) as %lq Hlq
    (try wp_auto)
    -- no queued items
    ihave IHq : iprop(∃ (x : Delta), "i" ∷ i_ptr ↦ (W64 0) ∗ "qi" ∷ queuedItem_ptr ↦ x) $$ [i queuedItem]
    · iexists _; iframe
    wp_for IHq
    (try wp_auto)
    -- no queued keys
    ihave IHk : iprop(∃ (x : GoString), "i" ∷ i_ptr ↦ (W64 0) ∗ "qk" ∷ queuedKey_ptr ↦ x) $$ [i queuedKey]
    · iexists _; iframe
    wp_for IHk
    (try wp_auto)
    -- the store's keys, read by the exclusive writer
    wp_bind
    iapply (wp_ListKeys ca ts γ OK Fam kf) $$ [$Hpkg $Hca $Hr]
    inext
    iapply (writer_read γ SW Rw σ HRw) $$ Hsw HSW
    iintro HSW %ksl ⟨%ks, %Hks, Hksl, Hr⟩
    ihave %Hklen := ownSlice_len _ _ _ $$ Hksl
    have hnk : ∀ k, (sets.insertAll ∅ (objs.map KF) !! k).isSome = decide (k ∈ objs.map KF) := by
      intro k; rw [sets.lookup_insertAll]; by_cases h : k ∈ objs.map KF <;> simp [h]
    (try wp_auto)
    -- the deletions: the store's keys the new items lack
    ihave IH3 : iprop(∃ (n : w64) (x : GoString),
        "i" ∷ i_ptr ↦ n ∗
        "kk" ∷ knownKey_ptr ↦ x ∗
        "HSW" ∷ SW σ ∗ "Hr" ∷ tsReader ts γ OK Fam ∗
        "HD" ∷ Dl (((ks.take (sint.nat n)).filter (fun k => decide (k ∉ objs.map KF))).map
          (fun k => tombstone k (objAt σ.items k))) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ks.length⌝) $$ [i knownKey HSW Hr HD]
    · iexists W64 0, _
      iframe
      ipureintro
      exact ⟨by decide, by simp⟩
    wp_for IH3
    wp_if_destruct
    · have Hlt : sint.nat n < ks.length := by word
      obtain ⟨k, Hk⟩ : ∃ k, ks[sint.nat n]? = some k := ⟨_, List.getElem?_eq_getElem Hlt⟩
      simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksl.len from ⟨Hn.1, Hif⟩, _root_.and_self,
        ↓reduceIte]
      wp_apply wp_load_slice_index ksl (sint.Z n) ks (DFrac.own 1) k Hn.1 $$ [Hksl] as Hksl
      · iframe; ipureintro; exact Hk
      have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
        have := Hn.1; have := Hlt; have := Hklen.1; word
      have h1 : 0 ≤ sint.Z (n + W64 1) := by have := Hn.1; have := Hlt; have := Hklen.1; word
      have Htake : ks.take (sint.nat (n + W64 1)) = ks.take (sint.nat n) ++ [k] := by
        rw [hn1, List.take_add_one, Hk]; rfl
      (try wp_auto)
      wp_apply (sets.Set.wp_ptr_Has_of wp_Has) $$ [$newKeys $Hnk] as ⟨newKeys, Hnk⟩
      rw [hnk k]
      by_cases hkn : k ∈ objs.map KF
      · rw [decide_eq_true hkn]
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, k
        iframe
        rw [Htake, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, hkn, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; exact ⟨h1, by omega⟩
      · rw [decide_eq_false hkn]
        (try wp_auto)
        wp_apply (wp_map_lookup2 (V := Delta) go.string Delta.ty lq ∅ k (DFrac.own 1)) $$ Hlq as Hlq
        (try wp_auto)
        have hkin : k ∈ σ.items := (Hks.2 k).1 (List.mem_of_getElem? Hk)
        wp_bind
        iapply (wp_GetByKey ca ts γ OK Fam kf k) $$ [$Hpkg $Hca $Hr]
        inext
        iapply (writer_read γ SW Rw σ HRw) $$ Hsw HSW
        iintro HSW %item %ok ⟨%Hitem, #Hokx, Hr⟩
        obtain ⟨rfl, rfl⟩ := Hitem
        rw [decide_eq_true hkin]
        (try wp_auto)
        ihave #Hod1 := Hod $$ %((((ks.take (sint.nat n)).filter
          (fun k => decide (k ∉ objs.map KF))).map (fun k => tombstone k (objAt σ.items k))))
          %k %(objAt σ.items k)
        wp_bind (App (Val #od) _)
        iapply Hod1 $$ [$HD $Hokx]
        inext
        iintro HD
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, k
        iframe
        rw [Htake, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, hkn, not_false_eq_true, decide_true,
          ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro; exact ⟨h1, by omega⟩
    · have hnl : sint.nat n = ks.length := by word
      rw [hnl, List.take_length]
      (try wp_auto)
      -- the replacements
      ihave IH4 : iprop(∃ (m : w64) (y : GoInterface),
          "j" ∷ i_ptr ↦ m ∗
          "ob" ∷ obj_ptr ↦ y ∗
          "HSW" ∷ SW σ ∗ "Hr" ∷ tsReader ts γ OK Fam ∗ "HR" ∷ Rl (objs.take (sint.nat m)) ∗
          "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.nat m ≤ objs.length⌝) $$ [i obj HSW Hr HR]
      · iexists W64 0, _
        iframe
        ipureintro
        exact ⟨by decide, by simp⟩
      wp_for IH4
      wp_if_destruct
      · have Hlt : sint.nat m < objs.length := by word
        obtain ⟨e, He⟩ : ∃ e, objs[sint.nat m]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
        simp only [show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z nsl.len from ⟨Hm.1, Hif⟩,
          _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index nsl (sint.Z m) objs dq e Hm.1 $$ [Hnsl] as Hnsl
        · iframe; ipureintro; exact He
        (try wp_auto)
        ihave #Horp1 := Horp $$ %(objs.take (sint.nat m)) %e
        wp_bind (App (Val #orp) _)
        iapply Horp1 $$ [$HR $HSW $Hr]
        · ipureintro; exact List.mem_of_getElem? He
        inext
        iintro ⟨HR, HSW, Hr⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists m + W64 1, e
        iframe
        have hm1 : sint.nat (m + W64 1) = sint.nat m + 1 := by
          have := Hm.1; have := Hlt; have := Hlen.1; word
        have h1 : 0 ≤ sint.Z (m + W64 1) := by have := Hm.1; have := Hlt; have := Hlen.1; word
        rw [hm1, List.take_add_one, He]
        simp only [Option.toList_some]
        iframe
        ipureintro; exact ⟨h1, by omega⟩
      · have hml : sint.nat m = objs.length := by word
        rw [hml, List.take_length]
        (try wp_auto)
        iapply HΦ
        iexists ks.filter (fun k => decide (k ∉ objs.map KF))
        iframe
        ipureintro
        refine ⟨Hks.1.filter _, fun k => ?_⟩
        rw [List.mem_filter, Hks.2 k]
        simp

end proof

end cache
end EtcdGrove
end Perennial
