module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialPrefixOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.initialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.eventsEqual
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

theorem initialPrefixOk.wp_proof
    (wp_initialEvents : initialEvents.spec (GF := GF) (hG := hG))
    (wp_histAt : histAt.spec (GF := GF) (hG := hG))
    (wp_eventsEqual : eventsEqual.spec (GF := GF) (hG := hG)) :
    initialPrefixOk.spec (GF := GF) (hG := hG) := by
  intro x req s evs c g Hrv
  wp_start as ⟨#Hs, #Hc⟩
  unfold wevsOwn cfgOwn storeOwn
  icases Hs with ⟨%ws, #Hk, %He⟩
  subst He
  icases Hc with ⟨⟨#Hst, %Hstrv⟩, #Hh, #Hp, %Hhl⟩
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  irename : (in_ptr ↦ x : IProp GF) => Hin
  wp_if_destruct
  · have hnil : ws = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1, Hif]; rfl)
    subst hnil
    rw [show initialPrefixOkL x (uint.nat req) (List.map wevOf []) g.st = true from rfl]
    iapply HΦ; itrivial
  have hne : ws ≠ [] := fun h => by subst h; simp at Hl; apply Hif; word
  (try wp_auto)
  wp_if_destruct
  all_goals
    ihave HI : (∃ rr : w64, "r" ∷ r_ptr ↦ rr ∗
        "%Hr" ∷ ⌜max (uint.nat req) 1 ≤ uint.nat rr ∧
          (uint.nat rr ≤ uint.nat g.st.st.rv + 1 ∨ uint.nat rr = max (uint.nat req) 1) ∧
          (List.range' (max (uint.nat req) 1) (uint.nat rr - max (uint.nat req) 1)).any
            (prefAt x (ws.map wevOf).length (ws.map wevOf) g.st) = false⌝ : IProp GF) $$ [r]
    · iexists _
      iframe
      ipureintro
      refine ⟨?_, Or.inr ?_, ?_⟩
      all_goals first | (simp_all; done) | (simp_all; word) | (word) |
        (rw [show ∀ a : Nat, a - a = 0 from Nat.sub_self]; rfl) | skip
    wp_for HI
    wp_if_destruct
    · have hle0 := Hif; clear Hif
      have hle : uint.Z rr ≤ uint.Z c.st'.rv' := by
        first
          | exact hle0
          | (exact Classical.byContradiction fun h => by
              rw [decide_eq_false h] at hle0; have := go.intoVal_inj hle0; simp at this)
      have hr1 : uint.nat (rr + W64 1) = uint.nat rr + 1 := by rw [Hstrv] at hle; word
      have hsnoc := range'_any_snoc (prefAt x (ws.map wevOf).length (ws.map wevOf) g.st)
        (max (uint.nat req) 1) (uint.nat rr) Hr.1
      wp_apply wp_histAt $$ [$Hh] as %sh #Hsh
      · ipureintro; exact Hhl
      (try wp_auto)
      wp_apply wp_initialEvents $$ [$Hsh] as %si Hi
      imod wevsOwnM_persist _ _ $$ Hi with #Hi
      ihave #Hi' : wevsOwn si (initialEventsL x (histAtL g.st.hist rr)) $$ [Hi]
      · iexact Hi
      unfold wevsOwn
      icases Hi with ⟨%is, #Hik, %Hie⟩
      ihave %Hil := ownSlice_len $$ Hik
      ihave %Hwf := ownSlice_wf _ _ _ $$ Hik
      have hpref : prefAt x (ws.map wevOf).length (ws.map wevOf) g.st (uint.nat rr) =
          (evsEqL ((initialEventsL x (histAtL g.st.hist rr)).take (ws.map wevOf).length)
            (ws.map wevOf) && decide ((ws.map wevOf).length ≤
              (initialEventsL x (histAtL g.st.hist rr)).length)) := rfl
      (try wp_auto)
      wp_if_destruct
      · have hn := Hif; clear Hif
        have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z si.len :=
          ⟨by word, by word, hn⟩
        (try wp_auto)
        rw [if_pos ⟨hb.1, hb.2.1, by word⟩]
        icases (ownSlice_slice (W64 0) s.len si DFrac.discard is hb).1 $$ Hik with ⟨-, #Hsub, -⟩
        (try wp_auto)
        ihave #Hea : wevsOwn (slice.slice si WEvent (W64 0) s.len)
            ((initialEventsL x (histAtL g.st.hist rr)).take (ws.map wevOf).length) $$ []
        · unfold wevsOwn
          iexists _
          isplit
          · iexact Hsub
          · ipureintro
            have h0 : sint.nat (W64 0) = 0 := rfl
            rw [← Hie, List.length_map, Hl.1]
            simp [subslice, List.map_take]
            rw [show sint.nat (0#64 : w64) = 0 from rfl, List.drop_zero]
        ihave #Heb : wevsOwn s (ws.map wevOf) $$ []
        · unfold wevsOwn; iexists ws; isplit; iexact Hk; ipureintro; rfl
        wp_apply (wp_eventsEqual _ s _ (ws.map wevOf)) $$ [$Hea $Heb]
        have hlen : (ws.map wevOf).length ≤ (initialEventsL x (histAtL g.st.hist rr)).length := by
          rw [← Hie]; simp only [List.length_map]; word
        cases heq : evsEqL ((initialEventsL x (histAtL g.st.hist rr)).take (ws.map wevOf).length)
            (ws.map wevOf)
        · (try wp_auto)
          wp_for_post
          iframe
          iexists rr + W64 1
          iframe
          ipureintro
          refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; rw [Hstrv] at hle; word), ?_⟩
          rw [hr1, hsnoc, Hr.2.2, hpref, heq]
          rfl
        · (try wp_auto)
          wp_for_post
          have hany : (List.range' (max (uint.nat req) 1) (uint.nat g.st.st.rv + 1 - max (uint.nat req) 1)).any
              (prefAt x (ws.map wevOf).length (ws.map wevOf) g.st) = true := by
            apply range'_any_mono _ _ (uint.nat rr + 1)
            · omega
            · rw [Hstrv] at hle; word
            · rw [hsnoc, hpref, heq, Bool.true_and, decide_eq_true hlen, Bool.or_true]
          rw [show initialPrefixOkL x (uint.nat req) (ws.map wevOf) g.st = true by
            unfold initialPrefixOkL
            rw [show (ws.map wevOf).isEmpty = false by simpa using hne]
            simpa [prefAt] using hany]
          iapply HΦ; itrivial
      · have hn := Hif; clear Hif
        wp_for_post
        iframe
        iexists rr + W64 1
        iframe
        ipureintro
        refine ⟨by rw [hr1]; omega, Or.inl (by rw [hr1]; rw [Hstrv] at hle; word), ?_⟩
        have hlen : ¬ (ws.map wevOf).length ≤ (initialEventsL x (histAtL g.st.hist rr)).length := by
          rw [← Hie]; simp only [List.length_map]; word
        rw [hr1, hsnoc, Hr.2.2, hpref, decide_eq_false hlen, Bool.and_false]
    · have hgt0 := Hif; clear Hif
      have hgt : ¬ uint.Z rr ≤ uint.Z c.st'.rv' := by
        first
          | exact hgt0
          | (intro h; apply hgt0; rw [decide_eq_true h])
      (try simp only [hgt, decide_False, decide_True, ↓reduceIte, eq_self_iff_true])
      (try wp_auto)
      rw [show initialPrefixOkL x (uint.nat req) (ws.map wevOf) g.st = false by
        unfold initialPrefixOkL
        rw [show (ws.map wevOf).isEmpty = false by simpa using hne, Bool.false_or]
        have : (List.range' (max (uint.nat req) 1) (uint.nat g.st.st.rv + 1 - max (uint.nat req) 1)).any
            (prefAt x (ws.map wevOf).length (ws.map wevOf) g.st) = false := by
          rcases Hr.2.1 with h | h
          · rw [show uint.nat g.st.st.rv + 1 = uint.nat rr by rw [Hstrv] at hgt; word]
            exact Hr.2.2
          · rw [show uint.nat g.st.st.rv + 1 - max (uint.nat req) 1 = 0 by rw [Hstrv] at hgt; word]
            rfl
        simpa [prefAt] using this]
      iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
