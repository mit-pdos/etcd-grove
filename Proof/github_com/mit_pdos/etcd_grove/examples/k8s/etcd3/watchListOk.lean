module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchListOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.firstBookmark
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialPrefixOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.eventsEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.reliableOk
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

theorem watchListOk.wp_proof
    (wp_firstBookmark : firstBookmark.spec (GF := GF) (hG := hG))
    (wp_initialPrefixOk : initialPrefixOk.spec (GF := GF) (hG := hG))
    (wp_histAt : histAt.spec (GF := GF) (hG := hG))
    (wp_initialEvents : initialEvents.spec (GF := GF) (hG := hG))
    (wp_eventsEqual : eventsEqual.spec (GF := GF) (hG := hG))
    (wp_reliableOk : reliableOk.spec (GF := GF) (hG := hG)) :
    watchListOk.spec (GF := GF) (hG := hG) := by
  intro x req s evs c g Hrv Hreq Hevs
  wp_start as ⟨#Hs, #Hc⟩
  ihave %Hstrv := cfgOwn_rv c g $$ Hc
  wp_auto
  wp_apply wp_firstBookmark $$ [$Hs] as %b %hb
  (try wp_auto)
  rcases hfi : evs.findIdx? (fun e => decide (e.t = 3)) with _ | k
  · rw [hfi] at hb
    wp_if_destruct
    · wp_apply (wp_initialPrefixOk x req s evs c g Hrv) $$ [$Hs $Hc]
      (try wp_auto)
      rw [show watchListOkL x (uint.nat req) evs g.st = initialPrefixOkL x (uint.nat req) evs g.st by
        unfold watchListOkL; rw [hfi]]
      iapply HΦ; itrivial
    · exfalso; word
  · rw [hfi] at hb
    obtain ⟨hklt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfi
    unfold wevsOwn
    icases Hs with ⟨%ws, #Hk, %He⟩
    subst He
    ihave %Hl := ownSlice_len $$ Hk
    have hklt' : k < ws.length := by simpa using hklt
    have hbk : sint.nat b = k := by word
    list_elem ws k as w
    have hwk : (ws.map wevOf)[k]? = some (wevOf w) := by simp [Hw_lookup]
    have hres := watchListOkL_some x (uint.nat req) (ws.map wevOf) g.st k (wevOf w) hfi hwk
    wp_if_destruct
    · exfalso; word
    have hbZ : 0 ≤ sint.Z b ∧ sint.Z b < sint.Z s.len := ⟨by word, by word⟩
    icases ownSlice_elem_acc (sint.Z b) w s _ ws hbZ.1 (by rw [← hbk] at Hw_lookup; simpa [sint.nat] using Hw_lookup)
      $$ Hk with ⟨#He, -⟩
    iStructNamedSuffix He "_e"
    iStructNamedSuffix Obj_e "_o"
    iterate 3 ((try simp only [hbZ, _root_.and_self, ↓reduceIte]); (try wp_auto))
    have hwo : (wevOf w).o = w.Obj' := rfl
    rw [hwo] at hres
    cases hA : w.Obj'.Annotated'
    · (try wp_auto)
      rw [hres, hA]
      simp only [Bool.not_false, ↓reduceIte]
      iapply HΦ; itrivial
    rw [hA] at hres
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hres
    iterate 3 ((try simp only [hbZ, _root_.and_self, ↓reduceIte]); (try wp_auto))
    have hfalse : ∀ (P : Prop), P → (P → (uint.nat req ≠ 0 ∧ uint.nat w.Obj'.ResourceVersion' < uint.nat req) ∨
        uint.nat w.Obj'.ResourceVersion' < 1 ∨ uint.nat g.st.st.rv < uint.nat w.Obj'.ResourceVersion') →
        watchListOkL x (uint.nat req) (ws.map wevOf) g.st = false := by
      intro P hP himp
      rw [hres]
      simp only [himp hP, ↓reduceIte]
    iterate 4
      all_goals (try wp_if_destruct)
      all_goals (try (iapply HΦ; fail))
      all_goals (try (rw [hfalse True trivial (fun _ => by rw [← Hstrv]; word)]
                      iapply HΦ
                      itrivial))
    all_goals
      rw [hres, if_neg (by rw [← Hstrv]; word)]
      ihave ⟨#Hh, %Hhl⟩ := cfgOwn_hist c g $$ Hc
      (try wp_auto)
      wp_apply wp_histAt $$ [$Hh] as %sh #Hsh
      · ipureintro; exact Hhl
      (try wp_auto)
      wp_apply wp_initialEvents $$ [$Hsh] as %si Hi
      imod wevsOwnM_persist _ _ $$ Hi with #Hi
      (try wp_auto)
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hk
      have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z b ∧ sint.Z b ≤ sint.Z s.len :=
        ⟨by word, by word, by word⟩
      icases (ownSlice_slice (W64 0) b s DFrac.discard ws hb1).1 $$ Hk with ⟨-, #Hpre, #Hsuf⟩
      have h0 : sint.nat (W64 0) = 0 := rfl
      ihave #Hea : wevsOwn (slice.slice s WEvent (W64 0) b) ((ws.map wevOf).take k) $$ []
      · unfold wevsOwn
        iexists _
        isplit
        · iexact Hpre
        · ipureintro
          rw [h0, hbk]
          simp [subslice, List.map_take]
      have hcap : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z b ∧ sint.Z b ≤ sint.Z s.cap :=
        ⟨hb1.1, hb1.2.1, by word⟩
      simp only [hcap, ↓reduceIte]
      (try wp_auto)
      wp_apply (wp_eventsEqual si _ (initialEventsL x (histAtL g.st.hist w.Obj'.ResourceVersion'))
        ((ws.map wevOf).take k)) $$ [$Hi $Hea]
      have hhist : histAtL g.st.hist w.Obj'.ResourceVersion' =
          histN g.st.hist (uint.nat w.Obj'.ResourceVersion') := rfl
      rw [hhist]
      cases heq : evsEqL (initialEventsL x (histN g.st.hist (uint.nat w.Obj'.ResourceVersion')))
          ((ws.map wevOf).take k)
      · (try wp_auto)
        simp only [Bool.not_false, ↓reduceIte]
        iapply HΦ; itrivial
      · (try wp_auto)
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hcap2 : 0 ≤ sint.Z b ∧ sint.Z b ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap :=
          ⟨by word, by word, by word⟩
        simp only [hcap2, ↓reduceIte]
        (try wp_auto)
        ihave #Hed : wevsOwn (slice.slice s WEvent b s.len) ((ws.map wevOf).drop k) $$ []
        · unfold wevsOwn
          iexists _
          isplit
          · iexact Hsuf
          · ipureintro
            rw [hbk, List.map_drop]
        wp_apply (wp_reliableOk x _ _ ((ws.map wevOf).drop k) c g Hrv Hreq
          (fun e he => by have := Hevs e (List.mem_of_mem_drop he); word)) $$ [$Hed $Hc]
        (try wp_auto)
        (try rw [show uint.nat (W64 0) = 0 from rfl])
        iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
