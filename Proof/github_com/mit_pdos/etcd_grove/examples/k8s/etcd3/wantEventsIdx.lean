module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.wantEventsIdx
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.viewFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.hview__at
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.changeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.keyInScope

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem wantEventsIdx.wp_proof
    (wp_changeAt : changeAt.spec (GF := GF) (hG := hG))
    (wp_toEvent : toEvent.spec (GF := GF) (hG := hG))
    (wp_viewFrom : viewFrom.spec (GF := GF) (hG := hG))
    (wp_at : hview.at.spec (GF := GF) (hG := hG))
    (wp_storeKey : storeKey.spec (GF := GF) (hG := hG))
    (wp_keyInScope : keyInScope.spec (GF := GF) (hG := hG)) :
    wantEventsIdx.spec (GF := GF) (hG := hG) := by
  intro x lo hi c g Hhl63 Hhi
  wp_start as #Hc
  unfold cfgOwn storeOwn
  icases Hc with ⟨⟨#Hst, %Hstrv⟩, #Hh, #Hp, %Hhl⟩
  wp_auto
  irename : (in_ptr ↦ x : IProp GF) => Hin
  wp_apply wp_max_u64 as %m1 %Hm1
  (try wp_auto)
  wp_apply wp_viewFrom _ _ _ Hhl63 $$ [$Hh] as %v #Hv
  (try wp_auto)
  wp_apply wp_max_u64 as %r0 %hr0
  (try wp_auto)
  have h2 : uint.nat (W64 2) = 2 := rfl
  rw [h2] at hr0 Hm1
  all_goals
    ihave HI : (∃ (rr : w64) (sl : GoSlice) (wl : List WEvent),
        "r" ∷ r_ptr ↦ rr ∗ "want" ∷ want_ptr ↦ sl ∗ "Hw" ∷ sl ↦* wl ∗
        "Hcap" ∷ ownSliceCap WEvent sl (DFrac.own 1) ∗
        "%Hr" ∷ ⌜max (uint.nat lo) 2 ≤ uint.nat rr ∧
          (uint.nat rr ≤ uint.nat hi ∨ uint.nat rr = max (uint.nat lo) 2) ∧
          wl.map wevOf = eventsInL x g.st.hist (max (uint.nat lo) 2) (uint.nat rr)⌝ : IProp GF)
        $$ [r want]
    · iexists r0, slice.nil, []
      iframe
      isplitl
      · iapply ownSlice_nil
      isplitl
      · iapply ownSliceCap_nil
      · ipureintro
        refine ⟨by omega, Or.inr hr0, ?_⟩
        rw [hr0]; unfold eventsInL; simp
    wp_for HI
    wp_if_destruct
    · have hlt := Hif; clear Hif
      have hr2 : 2 ≤ uint.nat rr := by omega
      have hrm1 : uint.nat (rr - W64 1) = uint.nat rr - 1 := by word
      have hr1 : uint.nat (rr + W64 1) = uint.nat rr + 1 := by word
      have hev : evAtL x g.st.hist (uint.nat rr) =
          (changeAtL (histAtL g.st.hist (rr - W64 1)).items (histAtL g.st.hist rr).items
            (uint.nat rr)).bind (fun ch =>
              if keyInScopeL x.WKey' x.Recursive' (storeKeyL ch.key) then toEventL x ch else none) := by
        unfold evAtL
        simp only [hr2, ↓reduceIte, histAtL_eq_histN, hrm1]
      have hsnoc := eventsInL_snoc x g.st.hist (max (uint.nat lo) 2) (uint.nat rr) Hr.1
      wp_method_call
      (try wp_auto)
      wp_apply wp_at $$ [$Hv] as %sp #Hsp
      · ipureintro; exact Hhl
      (try wp_auto)
      wp_method_call
      (try wp_auto)
      wp_apply wp_at $$ [$Hv] as %sc #Hsc
      · ipureintro; exact Hhl
      (try wp_auto)
      wp_apply (wp_changeAt sp sc (histAtL g.st.hist (rr - W64 1)) (histAtL g.st.hist rr) rr)
        $$ [$Hsp $Hsc] as %ch %ok %Hch
      (try wp_auto)
      rcases hca : changeAtL (histAtL g.st.hist (rr - W64 1)).items (histAtL g.st.hist rr).items
          (uint.nat rr) with _ | ch'
      · rw [hca] at Hch
        subst Hch
        (try wp_auto)
        wp_for_post
        iframe
        iexists rr + W64 1, sl, wl
        iframe
        ipureintro
        refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; word), ?_⟩
        rw [hr1, hsnoc, hev, hca, Hr.2.2]
        simp
      · rw [hca] at Hch
        obtain ⟨rfl, hchg⟩ := Hch
        have hkey : ch.key' = ch'.key := by rw [← hchg]; rfl
        (try wp_auto)
        wp_apply wp_storeKey
        (try wp_auto)
        wp_apply wp_keyInScope
        (try wp_auto)
        cases hks : keyInScopeL x.WKey' x.Recursive' (storeKeyL ch.key')
        · (try wp_auto)
          wp_for_post
          iframe
          iexists rr + W64 1, sl, wl
          iframe
          ipureintro
          refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; word), ?_⟩
          rw [hr1, hsnoc, hev, hca, Hr.2.2]
          simp [← hkey, hks]
        · (try wp_auto)
          wp_apply wp_toEvent as %ev %ok2 %Hte
          (try wp_auto)
          rw [hchg] at Hte
          rcases hte : toEventL x ch' with _ | e
          · rw [hte] at Hte
            subst Hte
            (try wp_auto)
            wp_for_post
            iframe
            iexists rr + W64 1, sl, wl
            iframe
            ipureintro
            refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; word), ?_⟩
            rw [hr1, hsnoc, hev, hca, Hr.2.2]
            simp [← hkey, hks, hte]
          · rw [hte] at Hte
            obtain ⟨rfl, hwe⟩ := Hte
            (try wp_auto)
            wp_apply wp_slice_literal (V := WEvent) (l := [ev])
            isplitr
            · ipureintro; rfl
            iintro %nsl ⟨Hn, -⟩
            wp_apply wp_slice_append $$ [$Hw $Hcap $Hn] as %sl' ⟨Hw', Hc', -⟩
            (try wp_auto)
            wp_for_post
            iframe
            iexists rr + W64 1, sl', wl ++ [ev]
            iframe
            ipureintro
            refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; word), ?_⟩
            rw [hr1, hsnoc, hev, hca, List.map_append, Hr.2.2]
            simp [← hkey, hks, hte, hwe]
    · (try wp_auto)
      iapply HΦ
      unfold wevsOwnM
      iexists wl
      iframe
      ipureintro
      rw [Hr.2.2, eventsInL_max2 x g.st.hist (uint.nat lo) (uint.nat hi)]
      rcases Hr.2.1 with h | h
      · rw [show uint.nat rr = uint.nat hi by word]
      · rw [h]
        unfold eventsInL
        rw [show uint.nat hi - max (uint.nat lo) 2 = 0 by word,
          show max (uint.nat lo) 2 - max (uint.nat lo) 2 = 0 by omega]

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
