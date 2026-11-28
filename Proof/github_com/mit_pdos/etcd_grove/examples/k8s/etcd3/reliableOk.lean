module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.eventsEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.evRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableLo
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.wantEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.nonBookmarks
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

theorem reliableOk.wp_proof
    (wp_eventsEqual : eventsEqual.spec (GF := GF) (hG := hG))
    (wp_evRange : evRange.spec (GF := GF) (hG := hG))
    (wp_reliableLo : reliableLo.spec (GF := GF) (hG := hG))
    (wp_wantEvents : wantEvents.spec (GF := GF) (hG := hG))
    (wp_nonBookmarks : nonBookmarks.spec (GF := GF) (hG := hG)) :
    reliableOk.spec (GF := GF) (hG := hG) := by
  intro x req s evs c g Hrv Hreq Hevs
  wp_start as ⟨#Hs, #Hc⟩
  unfold wevsOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  ihave %Hl := ownSlice_len $$ Hk
  ihave #Hs : wevsOwn s (ws.map wevOf) $$ []
  · unfold wevsOwn; iexists ws; isplit; iexact Hk; ipureintro; rfl
  wp_auto
  wp_if_destruct
  · have hnil : ws = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1, Hif]; rfl)
    subst hnil
    rw [show reliableOkL x (uint.nat req) (List.map wevOf []) g.st = true from rfl]
    iapply HΦ; itrivial
  have hne : ws.map wevOf ≠ [] := fun h => by simp at h; subst h; simp at Hl; apply Hif; word
  wp_apply wp_evRange s (ws.map wevOf) Hevs $$ [$Hs] as %lo %hi %hR
  have hR := hR hne
  (try wp_auto)
  wp_apply wp_reliableLo x req lo Hreq as %L %hL
  (try wp_auto)
  have hres := reliableOkL_eq x (uint.nat req) (ws.map wevOf) g.st _ _ hR
  rw [← hL] at hres
  ihave %Hstrv := cfgOwn_rv c g $$ Hc
  have hfalse : ∀ (P : Prop), P → (P → (x.Match' = W64 2 ∧ uint.nat req = 0) ∨
      (¬ (x.Match' = W64 2 ∧ uint.nat req = 0) ∧ uint.nat g.st.st.rv + 1 < uint.nat hi)) →
      reliableOkL x (uint.nat req) (ws.map wevOf) g.st = false := by
    intro P hP himp
    rw [hres]
    rcases himp hP with h1 | ⟨h1, h2⟩
    · simp [h1]
    · simp [h1, h2]
  iterate 3
    all_goals (try wp_if_destruct)
    all_goals (try (rw [hfalse True trivial (fun _ => by
                      first
                        | (left; constructor <;> first | assumption | word)
                        | (right; refine ⟨fun h => ?_, ?_⟩
                           · obtain ⟨h1, h2⟩ := h
                             first | (simp_all; done) | word
                           · rw [← Hstrv]; word))]
                    iapply HΦ
                    itrivial))
  all_goals
    have hnx : ¬ (x.Match' = W64 2 ∧ uint.nat req = 0) := fun h => by
      obtain ⟨h1, h2⟩ := h
      first | (simp_all; done) | word
    have hhi : ¬ (uint.nat g.st.st.rv + 1 < uint.nat hi) := by rw [← Hstrv]; word
    have hhi2 : uint.Z hi ≤ 2 ^ 63 := by rw [← Hstrv] at Hrv; word
    rw [hres, ite_eq_right_iff.mpr (fun h => absurd h hnx), ite_eq_right_iff.mpr (fun h => absurd h hhi)]
    (try wp_auto)
    wp_apply wp_wantEvents x L hi c g hhi2 $$ [$Hc] as %sw Hw
    imod wevsOwnM_persist _ _ $$ Hw with #Hw
    (try wp_auto)
    wp_apply wp_nonBookmarks $$ [$Hs] as %sn Hn
    imod wevsOwnM_persist _ _ $$ Hn with #Hn
    (try wp_auto)
    have hf : (fun e : WEv => decide (e.t ≠ 3)) = (fun e => !decide (e.t = 3)) := by
      funext e; simp
    wp_apply (wp_eventsEqual sw sn (eventsInL x g.st.hist (uint.nat L) (uint.nat hi))
      ((ws.map wevOf).filter fun e => !decide (e.t = 3))) $$ [$Hw $Hn]
    (try wp_auto)
    rw [hf]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
