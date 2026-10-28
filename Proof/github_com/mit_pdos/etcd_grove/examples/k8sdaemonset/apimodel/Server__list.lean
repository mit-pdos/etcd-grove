/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/Server__list.lean`.
Lean-first. The linearization point is the taking of the lock (the range then reads the state the lock
invariant holds; a flagged failure or a selector fires the caller's update at whatever state).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__list
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Server__chance
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.copyObject
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewBadRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.rvString
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.SrvLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem take_succ_filterMap {keys : List Key} {i : Int} (key : Key) (hi : 0 ≤ i)
    (hk : keys[i.toNat]? = some key) (f : Key → Option Obj) :
    (keys.take (i + 1).toNat).filterMap f = (keys.take i.toNat).filterMap f ++ (f key).toList := by
  rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk]
  cases h : f key <;> simp [List.filterMap_append, h]

theorem lo_sel (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.ListOptions) (dq : DFrac)
    (lo : kd.meta.ListOptions) :
    kd.meta.ListOptions.own (GF := GF) opts dq lo ⊢ kd.meta.ListOptions.own opts dq lo ∗
      ⌜opts.LabelSelector' = lo.LabelSelector' ∧ opts.FieldSelector' = lo.FieldSelector'⌝ := by
  unfold kd.meta.ListOptions.own
  iintro ⟨HT, %h1, %h2, Hr⟩
  iframe
  ipureintro; simp_all

theorem Server.list.wp_proof
    (wp_chance : Server.chance.spec (GF := GF) (hG := hG))
    (wp_copyObject : copyObject.spec (GF := GF) (hG := hG))
    (wp_rvString : rvString.spec (GF := GF) (hG := hG))
    (wp_NewInternalError : apierrors.NewInternalError.spec (GF := GF) (hG := hG))
    (wp_NewBadRequest : apierrors.NewBadRequest.spec (GF := GF) (hG := hG))
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    Server.list.spec (GF := GF) (hG := hG) := by
  intro _ s γ cfg r t ns opts dq lo admin
  wp_start as ⟨#Hs, #Ht, Ho⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors $$ []
  · iPkgInit
  ihave #Hstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Hinit : (github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.apimodelInit :
    IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%eS, #HeS⟩, ⟨%eR, #HeR⟩, ⟨%sA, #HeA⟩⟩
  ihave #Hsrv := Hs
  iunfold isServer at Hs
  icases Hs with ⟨%L, #Hs⟩
  ihave %Htl := srvFixed_tableOf s γ L cfg r t $$ [$Hs $Ht]
  subst Htl
  ihave ⟨#Hfx, -⟩ := srvFixed_tbl s γ L cfg r $$ Hs
  iunfold tableFixed at Hfx
  icases Hfx with ⟨#Hres, #Hnsd, #Hobjs, #Hemp, -⟩
  iNamed Hs
  iNamed Hcfg
  icases lo_sel opts dq lo $$ Ho with ⟨Ho, %Hsel⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_if_destruct
  · wp_if_destruct
    · wp_apply wp_chance $$ [$Hsrv] as %b %Hb
      have hns : ¬ (lo.LabelSelector' ≠ go!"" ∨ lo.FieldSelector' ≠ go!"") := by
        rw [← Hsel.1, ← Hsel.2]; simp_all
      cases b
      · wp_auto
        wp_apply wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
        iunfold lockInv at Hinv
        icases Hinv with ⟨%σ0, %H, Hlk, Hhist, %Hok, Hws⟩
        iNamed Hlk
        icases tablesLocked_acc L σ0 r $$ Htbls with ⟨Ht0, Hback⟩
        iunfold tableLocked at Ht0
        icases Ht0 with ⟨%M, %sl, %cs, HM, Hrel, Hlog, Hsl, Hcap, Hcs⟩
        ihave #Hpast := pastSt_of_auth γ _ H σ0 Hok $$ Hhist
        imod (au_read γ H σ0 (fun σ => iprop(∀ sl rv err, kd.meta.ListOptions.own opts dq lo ∗
          listRet γ cfg.FailReads' admin r ns lo σ sl rv err -∗ Φ (PairV (PairV #sl #rv) #err))))
          $$ [$Hhist $HΦ] with ⟨Hhist, HΦ⟩
        wp_func_lits
        wp_bind (App (App (Val (map.forRange _ _)) _) _)
        iapply wp_map_for_range (fun (keys : List Key) (i : Int) => iprop(∃ (osl : GoSlice)
            (xs : List GoInterface) (ox : GoInterface) (kx : Key),
            "%Hi" ∷ ⌜0 ≤ i⌝ ∗
            "out" ∷ out_ptr ↦ osl ∗ "Hosl" ∷ osl ↦* xs ∗
            "Hocap" ∷ ownSliceCap apimodel.object osl (DFrac.own 1) ∗
            "Hxs" ∷ ([∗list] x;o ∈ xs;(keys.take i.toNat).filterMap
              (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none), objAt x (DFrac.own 1) o) ∗
            "obj" ∷ obj_ptr ↦ ox ∗ "key" ∷ key_ptr ↦ kx ∗ "ns" ∷ ns_ptr ↦ ns ∗
            "Hrel" ∷ objsRel M (σ0.tbl r).objs)) $$ HM
        iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
        isplitl [out obj key ns Hrel]
        · iexists slice.nil, [], _, _
          simp only [named]
          iframe
          isplitr
          · ipureintro; exact Int.le_refl _
          isplitr
          · iapply ownSlice_nil
          isplitr
          · iapply ownSliceCap_nil
          simp only [Int.toNat_zero, List.take_zero, List.filterMap_nil]
          iapply BigSepL2.bigSepL2_nil.2; itrivial
        isplitr
        · imodintro
          iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
          iNamed HP
          wp_auto
          icases objsRel_lookup M (σ0.tbl r).objs key v Hv $$ Hrel with ⟨%o, %ho, Hx, Hrelb⟩
          have hstep := take_succ_filterMap key Hi Hkey
            (fun k => if inNs ns k then (σ0.tbl r).objs !! k else none)
          wp_if_destruct
          · 
            wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
            ihave Hrel := Hrelb $$ Hx
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %l1 ⟨Hl1, _⟩
            simp only [go.arrayLiteralSize, List.foldl]
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
            (try wp_auto)
            unfold forMapPostcondition
            iright; ileft
            isplitr
            · ipureintro; rfl
            iexists osl', xs ++ [y], _, _
            simp only [named]
            rw [hstep]
            simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
            iframe
            isplitr
            · ipureintro; omega
            iapply BigSepL2.bigSepL2_nil.2; itrivial
          · wp_if_destruct
            · 
              wp_apply wp_copyObject $$ Hx as %y ⟨Hx, Hy⟩
              ihave Hrel := Hrelb $$ Hx
              wp_apply wp_slice_literal
              isplitr
              · ipureintro; rfl
              iintro %l1 ⟨Hl1, _⟩
              simp only [go.arrayLiteralSize, List.foldl]
              (try wp_auto)
              wp_apply wp_slice_append $$ [$Hosl $Hocap $Hl1] as %osl' ⟨Hosl, Hocap, -⟩
              (try wp_auto)
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists osl', xs ++ [y], _, _
              simp only [named]
              rw [hstep]
              simp only [inNs, _root_.decide_true, Bool.true_or, Bool.or_true, ↓reduceIte, ho, Option.toList_some]
              iframe
              isplitr
              · ipureintro; omega
              iapply BigSepL2.bigSepL2_nil.2; itrivial
            · have hin : inNs ns key = false := by
                simp only [inNs, Bool.or_eq_false_iff, decide_eq_false_iff_not]
                exact ⟨by assumption, by assumption⟩
              ihave Hrel := Hrelb $$ Hx
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists osl, xs, _, _
              simp only [named]
              rw [hstep]
              simp only [hin, Bool.false_eq_true, ↓reduceIte, Option.toList_none, List.append_nil]
              iframe
              ipureintro; omega
        iintro HP HM
        iNamed HP
        ihave %hdom := (BigSepM2.bigSepM2_lookup_iff (PROP := IProp GF)) $$ Hrel
        have hmem : ∀ k, k ∈ keys ↔ ((σ0.tbl r).objs !! k).isSome := fun k => (Hkset k).trans (hdom k)
        have hperm := perm_keys_filterMap (σ0.tbl r).objs keys Hknodup hmem (inNs ns)
        have htk : keys.take ((GMap.size M : Nat) : Int).toNat = keys := by
          rw [Int.toNat_natCast, ← Hklen, List.take_length]
        wp_auto
        wp_apply wp_rvString $$ [$Hstrconv]
        (try wp_auto)
        wp_apply wp_Unlock $$ [$Hmu $Hown Hhist Hws Hrev Huids Hrvsm Hrc Hback HM Hrel Hlog Hsl Hcap Hcs]
        · iunfold lockInv
          iexists σ0, H
          iframe
          iunfold srvLocked
          iframe
          ihave Htb := Hback $$ %σ0 %(fun _ _ => rfl) [HM Hrel Hlog Hsl Hcap Hcs]
          · iunfold tableLocked
            iexists M, sl, cs
            iframe
          iframe
          ipureintro; exact ⟨Huidlt, Hok⟩
        iapply HΦ
        iframe
        unfold listRet
        rw [if_neg hns]
        iright
        isplitr
        · ipureintro; rfl
        unfold listedAt
        iexists xs, _
        iframe
        iframe #
        ipureintro
        refine ⟨?_, rfl⟩
        unfold listOk
        rw [htk]
        exact hperm
      · imod (au_read_any γ (fun σ => iprop(∀ sl rv err, kd.meta.ListOptions.own opts dq lo ∗
          listRet γ cfg.FailReads' admin r ns lo σ sl rv err -∗ Φ (PairV (PairV #sl #rv) #err)))) $$ HΦ
          with ⟨%σ, HΦ⟩
        wp_auto
        wp_apply +noauto wp_NewInternalError as %p ⟨%st, Hp, %Hst⟩
        ipersist Hp
        wp_auto
        iapply HΦ
        iframe
        unfold listRet
        rw [if_neg hns]
        ileft
        isplitr
        · ipureintro; exact Hb rfl
        unfold errIs
        iexists p, st
        iframe #
        ipureintro
        exact ⟨rfl, Hst.2.1, Hst.2.2⟩
    · -- a field selector
      wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
      ipersist Hp
      imod (au_read_any γ (fun σ => iprop(∀ sl rv err, kd.meta.ListOptions.own opts dq lo ∗
        listRet γ cfg.FailReads' admin r ns lo σ sl rv err -∗ Φ (PairV (PairV #sl #rv) #err)))) $$ HΦ
        with ⟨%σ, HΦ⟩
      wp_auto
      iapply HΦ
      iframe
      unfold listRet
      rw [if_pos (by right; rw [← Hsel.2]; exact Hif)]
      unfold errIs
      iexists p, st
      iframe #
      ipureintro
      exact ⟨rfl, Hst.2.1, Hst.2.2⟩
  · -- a label selector
    wp_apply +noauto wp_NewBadRequest as %p ⟨%st, Hp, %Hst⟩
    ipersist Hp
    imod (au_read_any γ (fun σ => iprop(∀ sl rv err, kd.meta.ListOptions.own opts dq lo ∗
      listRet γ cfg.FailReads' admin r ns lo σ sl rv err -∗ Φ (PairV (PairV #sl #rv) #err)))) $$ HΦ
      with ⟨%σ, HΦ⟩
    wp_auto
    iapply HΦ
    iframe
    unfold listRet
    rw [if_pos (by left; rw [← Hsel.1]; exact Hif)]
    unfold errIs
    iexists p, st
    iframe #
    ipureintro
    exact ⟨rfl, Hst.2.1, Hst.2.2⟩

end proof

end apimodel
end EtcdGrove
end Perennial
