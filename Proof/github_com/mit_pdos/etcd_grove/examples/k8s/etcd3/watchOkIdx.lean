module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOkIdx
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decodeWEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.checkedEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bookmarksOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.parseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchListOkIdx
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableOkIdx
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.HView

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

theorem watchOkIdx.wp_proof
    (wp_decodeWEvents : decodeWEvents.spec (GF := GF) (hG := hG))
    (wp_checkedEvents : checkedEvents.spec (GF := GF) (hG := hG))
    (wp_bookmarksOk : bookmarksOk.spec (GF := GF) (hG := hG))
    (wp_parseRV : parseRV.spec (GF := GF) (hG := hG))
    (wp_watchListOkIdx : watchListOkIdx.spec (GF := GF) (hG := hG))
    (wp_reliableOkIdx : reliableOkIdx.spec (GF := GF) (hG := hG)) :
    watchOkIdx.spec (GF := GF) (hG := hG) := by
  intro x y c g Hhl63 Hrv Hreq
  wp_start as #Hc
  ihave %Hstrv := cfgOwn_rv c g $$ Hc
  wp_auto
  have hret : (y.WFailed' || x.Skip') = true → watchOkL x y g.st = true := fun h => by
    unfold watchOkL; rw [h]; rfl
  cases hW : y.WFailed'
  case true =>
    (try wp_auto)
    rw [hret (by simp [hW])]
    iapply HΦ; itrivial
  (try wp_auto)
  cases hS : x.Skip'
  case true =>
    (try wp_auto)
    rw [hret (by simp [hS])]
    iapply HΦ; itrivial
  (try wp_auto)
  have hf : (y.WFailed' || x.Skip') = false := by simp [hW, hS]
  wp_apply wp_decodeWEvents as %sl %ok Hd
  rcases hd : decWEventsL y.WEvents' with _ | all
  · icases Hd with %Hok
    subst Hok
    (try wp_auto)
    rw [show watchOkL x y g.st = false by unfold watchOkL; rw [hf, hd]; rfl]
    iapply HΦ; itrivial
  icases Hd with ⟨%Hok, Hw⟩
  subst Hok
  imod wevsOwnM_persist _ _ $$ Hw with #Hw
  (try wp_auto)
  have hty : ∀ e ∈ all, e.t < 2 ^ 63 := fun e he => by
    have := decWEventsL_t y.WEvents'.length y.WEvents' (Nat.le_refl _) all hd e he; omega
  wp_apply (wp_checkedEvents sl all c.st'.rv' hty) $$ [$Hw] as %se %ok2 Hce
  rw [Hstrv]
  cases hrj : rejectsL all (uint.nat g.st.st.rv)
  case true =>
    simp only [↓reduceIte]
    icases Hce with %Hok2
    subst Hok2
    (try wp_auto)
    rw [watchOkL_false x y g.st all hf hd (Or.inl hrj)]
    iapply HΦ; itrivial
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hce with ⟨%Hok2, Hk⟩
  subst Hok2
  imod wevsOwnM_persist _ _ $$ Hk with #Hk
  (try wp_auto)
  wp_apply wp_bookmarksOk $$ [$Hk]
  cases hbk : bookmarksOkL (keptL all)
  case false =>
    (try wp_auto)
    rw [watchOkL_false x y g.st all hf hd (Or.inr (Or.inl ⟨hrj, hbk⟩))]
    iapply HΦ; itrivial
  (try wp_auto)
  wp_apply wp_parseRV as %n %err Hp
  rcases hp : parseRVD x.MinRV' with _ | reqw
  · icases Hp with ⟨%Herr, -⟩
    cases err with
    | nil => exact absurd rfl Herr
    | ok i =>
      (try wp_auto)
      rw [watchOkL_false x y g.st all hf hd (Or.inr (Or.inr ⟨hrj, hp⟩))]
      iapply HΦ; itrivial
  icases Hp with %Hp
  obtain ⟨rfl, rfl⟩ := Hp
  (try wp_auto)
  have hkept : ∀ e ∈ keptL all, uint.nat e.o.ResourceVersion' ≤ uint.nat g.st.st.rv := by
    intro e he
    unfold rejectsL at hrj
    simp only [Bool.or_eq_false_iff] at hrj
    have h2 := hrj.2
    rw [List.any_eq_false] at h2
    have := h2 e he
    simp at this
    omega
  have hres := watchOkL_eq x y g.st all n hf hd hrj hbk hp
  wp_if_destruct
  · wp_apply (wp_watchListOkIdx x n se (keptL all) c g Hhl63 Hrv (Hreq n hp) hkept) $$ [$Hk $Hc]
    (try wp_auto)
    rw [hres, if_pos Hif]
    iapply HΦ; itrivial
  · wp_apply (wp_reliableOkIdx x n se (keptL all) c g Hhl63 Hrv (Hreq n hp)
      (fun e he => by have := hkept e he; word)) $$ [$Hk $Hc]
    (try wp_auto)
    rw [hres, if_neg Hif]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
