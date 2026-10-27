/-
Proof of `Spec/k8s_io/client_go/tools/cache/processDeltas.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processDeltas
public import Spec.k8s_io.client_go.tools.cache.cache__Get
public import Spec.k8s_io.client_go.tools.cache.cache__Add
public import Spec.k8s_io.client_go.tools.cache.cache__Update
public import Spec.k8s_io.client_go.tools.cache.cache__Delete
public import Spec.k8s_io.client_go.tools.cache.cache__Bookmark

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem processDeltas.wp_proof
    (wp_pRAI : processReplacedAllInfo.spec (GF := GF) (hG := hG))
    (wp_Get : cache.Get.spec (GF := GF) (hG := hG))
    (wp_Add : cache.Add.spec (GF := GF) (hG := hG))
    (wp_Update : cache.Update.spec (GF := GF) (hG := hG))
    (wp_Delete : cache.Delete.spec (GF := GF) (hG := hG))
    (wp_Bookmark : cache.Bookmark.spec (GF := GF) (hG := hG)) :
    processDeltas.spec (GF := GF) (hG := hG) := by
  intro lg h ca ts γ OK Fam kf kf' KF rvOf SW σ H evs d v sl b
  wp_start as ⟨#Hca, Hr, #Hsw, HSW, #Hh, HH, Hfd, Hsl, %Hkind, #Hkey, #Hkey', #Hacc⟩
  (try wp_auto)
  iunfold handlerOk at Hh
  icases Hh with ⟨%hi, %hh, #HonAdd, #HonUpd, #HonDel⟩
  subst hh
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.nat sl.len = 1 := by have := Hlen.1; simpa using this.symm
  have hsl0 := Hlen.2
  ihave IH : iprop(∃ (n : w64) (x : Delta),
      "i" ∷ i_ptr ↦ n ∗ "d" ∷ d_ptr ↦ x ∗ "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ 1⌝ ∗
      "Hst" ∷ (if sint.nat n = 0 then
        iprop(SW σ ∗ H evs ∗ fdAt OK d v ∗ tsReader ts γ OK Fam)
      else iprop(∃ (σ' : St) (evs' : List Ev), ⌜stepFD KF rvOf b σ d σ' evs'⌝ ∗
        SW σ' ∗ H (evs ++ evs') ∗ tsReader ts γ OK Fam))) $$ [i d HSW HH Hfd Hr]
  · iexists W64 0, _
    simp only [named]
    rw [ite_eq_left_of_eq_true _ _ (by simp)]
    iframe
    ipureintro; exact ⟨by decide, by decide⟩
  wp_for IH
  wp_if_destruct
  · have hn0 : sint.nat n = 0 := by word
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len by word, _root_.and_self,
      ↓reduceIte]
    rw [ite_eq_left_of_eq_true _ _ (by simp [hn0])]
    icases Hst with ⟨HSW, HH, Hfd, Hr⟩
    wp_apply wp_load_slice_index sl (sint.Z n) [v] (DFrac.own 1) v (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [show (sint.Z n).toNat = 0 from hn0]; rfl
    (try wp_auto)
    have hn1 : ¬ sint.nat (n + W64 1) = 0 := by word
    have hn1' : 0 ≤ sint.Z (n + W64 1) ∧ sint.nat (n + W64 1) ≤ 1 := by word
    cases d with
    | obj t o =>
      iunfold fdAt at Hfd
      icases Hfd with ⟨%Hv, #HOKo⟩
      obtain ⟨rfl, ty, w, ho⟩ := Hv
      simp only [FD.kindOk] at Hkind
      rcases Hkind with rfl | rfl | rfl
      · rw [decide_eq_false (by simp)]
        (try wp_auto)
        have hoin : o ∈ (FD.obj go!"Added" o).objs := List.mem_singleton_self o
        wp_bind
        iapply (wp_Get ca ts γ OK Fam kf _ KF o) $$ [$Hpkg $Hca $Hkey $Hr]
        · imodintro; ipureintro; exact hoin
        inext
        iapply (writer_read γ SW σ) $$ Hsw HSW
        iintro HSW %item %ok ⟨%Hitem, #Hold, Hr⟩
        obtain ⟨rfl, rfl⟩ := Hitem
        (try wp_auto)
        by_cases hin : KF o ∈ σ.items
        · rw [decide_eq_true hin]
          (try wp_auto)
          wp_bind
          iapply (wp_Update ca ts γ OK Fam kf _ KF rvOf o) $$ [$Hpkg $Hca $Hkey $Hacc $HOKo]
          · imodintro; ipureintro; exact hoin
          inext
          iapply (writer_step γ SW σ (fun σ => σ.update (KF o) o (rvOf o))) $$ Hsw HSW
          iintro HSW -
          (try wp_auto)
          ihave #HonUpd1 := HonUpd $$ %evs %(objAt σ.items (KF o)) %o
          wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
          iapply HonUpd1 $$ [$HH $Hold $HOKo]
          inext
          iintro HH
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          rw [ite_eq_right hn1]
          iframe
          ipureintro
          refine ⟨hn1', Or.inr ⟨by simp, rfl, ?_⟩⟩
          unfold putEv; rw [ite_eq_left hin]
        · rw [decide_eq_false hin]
          (try wp_auto)
          wp_bind
          iapply (wp_Add ca ts γ OK Fam kf _ KF rvOf o) $$ [$Hpkg $Hca $Hkey $Hacc $HOKo]
          · imodintro; ipureintro; exact hoin
          inext
          iapply (writer_step γ SW σ (fun σ => σ.update (KF o) o (rvOf o))) $$ Hsw HSW
          iintro HSW -
          (try wp_auto)
          ihave #HonAdd1 := HonAdd $$ %evs %o %b
          wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
          iapply HonAdd1 $$ [$HH $HOKo]
          inext
          iintro HH
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          rw [ite_eq_right hn1]
          iframe
          ipureintro
          refine ⟨hn1', Or.inr ⟨by simp, rfl, ?_⟩⟩
          unfold putEv; rw [ite_eq_right hin]
      · rw [decide_eq_false (by simp)]
        (try wp_auto)
        have hoin : o ∈ (FD.obj go!"Updated" o).objs := List.mem_singleton_self o
        wp_bind
        iapply (wp_Get ca ts γ OK Fam kf _ KF o) $$ [$Hpkg $Hca $Hkey $Hr]
        · imodintro; ipureintro; exact hoin
        inext
        iapply (writer_read γ SW σ) $$ Hsw HSW
        iintro HSW %item %ok ⟨%Hitem, #Hold, Hr⟩
        obtain ⟨rfl, rfl⟩ := Hitem
        (try wp_auto)
        by_cases hin : KF o ∈ σ.items
        · rw [decide_eq_true hin]
          (try wp_auto)
          wp_bind
          iapply (wp_Update ca ts γ OK Fam kf _ KF rvOf o) $$ [$Hpkg $Hca $Hkey $Hacc $HOKo]
          · imodintro; ipureintro; exact hoin
          inext
          iapply (writer_step γ SW σ (fun σ => σ.update (KF o) o (rvOf o))) $$ Hsw HSW
          iintro HSW -
          (try wp_auto)
          ihave #HonUpd1 := HonUpd $$ %evs %(objAt σ.items (KF o)) %o
          wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
          iapply HonUpd1 $$ [$HH $Hold $HOKo]
          inext
          iintro HH
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          rw [ite_eq_right hn1]
          iframe
          ipureintro
          refine ⟨hn1', Or.inr ⟨by simp, rfl, ?_⟩⟩
          unfold putEv; rw [ite_eq_left hin]
        · rw [decide_eq_false hin]
          (try wp_auto)
          wp_bind
          iapply (wp_Add ca ts γ OK Fam kf _ KF rvOf o) $$ [$Hpkg $Hca $Hkey $Hacc $HOKo]
          · imodintro; ipureintro; exact hoin
          inext
          iapply (writer_step γ SW σ (fun σ => σ.update (KF o) o (rvOf o))) $$ Hsw HSW
          iintro HSW -
          (try wp_auto)
          ihave #HonAdd1 := HonAdd $$ %evs %o %b
          wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
          iapply HonAdd1 $$ [$HH $HOKo]
          inext
          iintro HH
          (try wp_auto)
          wp_for_post
          iframe
          iexists n + W64 1, _
          simp only [named]
          rw [ite_eq_right hn1]
          iframe
          ipureintro
          refine ⟨hn1', Or.inr ⟨by simp, rfl, ?_⟩⟩
          unfold putEv; rw [ite_eq_right hin]
      · rw [decide_eq_false (by simp)]
        (try wp_auto)
        have hoin : o ∈ (FD.obj go!"Deleted" o).objs := List.mem_singleton_self o
        wp_bind
        iapply (wp_Delete ca ts γ OK Fam kf _ KF rvOf o) $$ [$Hpkg $Hca $Hkey $Hacc $HOKo]
        · imodintro; ipureintro; exact hoin
        inext
        iapply (writer_step γ SW σ (fun σ => σ.delete (KF o) (rvOfObj rvOf o))) $$ Hsw HSW
        iintro HSW -
        (try wp_auto)
        ihave #HonDel1 := HonDel $$ %evs %o
        wp_bind (App (Val #(methods hi.ty go!"OnDelete" hi.v)) _)
        iapply HonDel1 $$ [$HH]
        · iunfold delOk; ileft; iexact HOKo
        inext
        iintro HH
        (try wp_auto)
        wp_for_post
        iframe
        iexists n + W64 1, _
        simp only [named]
        rw [ite_eq_right hn1]
        iframe
        ipureintro
        exact ⟨hn1', Or.inl ⟨rfl, rfl, rfl⟩⟩
    | replaced objs rv =>
      iunfold fdAt at Hfd
      icases Hfd with ⟨%isl, %Hv, Hisl, #Hoks⟩
      subst Hv
      rw [decide_eq_true (by simp)]
      (try wp_auto)
      simp only [FD.objs]
      wp_apply (wp_pRAI lg (GoInterface.ok hi) ca ts γ OK Fam kf kf' KF SW σ H evs rv isl objs b)
        $$ [$Hpkg $Hca $Hr $Hsw $HSW $HH $Hisl $Hoks $Hkey $Hkey']
        as ⟨%dks, %Hdks, HSW, HH, Hisl, Hr⟩
      · iunfold handlerOk; iexists hi; iframe #; ipureintro; rfl
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _
      simp only [named]
      rw [ite_eq_right hn1]
      iframe
      ipureintro
      exact ⟨hn1', rfl, dks, Hdks.1, Hdks.2, rfl⟩
    | bookmark rv =>
      iunfold fdAt at Hfd
      icases Hfd with %Hv
      subst Hv
      rw [decide_eq_false (by simp)]
      (try wp_auto)
      wp_bind
      iapply (wp_Bookmark ca ts γ OK Fam kf rv) $$ [$Hpkg $Hca]
      inext
      iapply (writer_step γ SW σ (fun σ => σ.bookmark rv)) $$ Hsw HSW
      iintro HSW -
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _
      simp only [named]
      rw [ite_eq_right hn1]
      iframe
      isplitr
      · ipureintro; exact hn1'
      iexists []
      rw [List.append_nil]
      iframe
      ipureintro
      exact ⟨rfl, rfl⟩
  · have hn1 : sint.nat n = 1 := by word
    simp only [show ¬ sint.nat n = 0 by omega, ↓reduceIte]
    icases Hst with ⟨%σ', %evs', %Hstep, HSW, HH, Hr⟩
    (try wp_auto)
    iapply HΦ
    iexists σ', evs'
    iframe
    ipureintro; exact Hstep

end proof

end cache
end EtcdGrove
end Perennial
