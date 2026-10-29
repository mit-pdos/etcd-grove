/- Lean-first (no Rocq counterpart). The proof of `Collect` (watchkv's `collect`'s, at the caller's
model and response facts, 2026-10-22, D33): the loop over the watch channel
(`wp_etcdWatch_receive`), each response's events by the caller's `Hresp`, the inner loop appending
them. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Collect
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem Collect.wp_proof (wp_Err : WatchResponse.Err.spec (GF := GF) (hG := hG)) :
    Collect.spec (GF := GF) (hG := hG) := by
  intro CS Ok F A wch γ upTo hP Hce Hresp
  haveI : ∀ (c c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
    Persistent (Ok c c' v r) := hP
  wp_start as ⟨#Hw, Hcons, #HA⟩
  (try wp_auto)
  wp_if_destruct
  · -- `upTo == 0`: no event needed
    (try wp_auto)
    iapply HΦ
    iintro -
    iexists []
    isplitr
    · iapply ownSlice_nil
    isplitr
    · ipureintro; simp
    iintro !> %i %e %h
    simp at h
  (try wp_auto)
  ihave IH : (∃ (evs0 : List wev) (sl : GoSlice) (lv : w64) (m : Nat) (c : w64),
      "evs" ∷ evs_ptr ↦ sl ∗ "last" ∷ last_ptr ↦ lv ∗ "Hs" ∷ sl ↦* evs0 ∗
      "Hcap" ∷ ownSliceCap wev sl (DFrac.own 1) ∗ "Hcons" ∷ etcdWatchConsumer γ m c ∗
      "%Hc" ∷ ⌜Cur evs0.length c ∧ ∀ e, evs0.getLast? = some e → lv = e.Rev'⌝ ∗
      "#Hrevs" ∷ □ ∀ (i : Nat) (e : wev), ⌜evs0[i]? = some e⌝ -∗ F i e :
      IProp GF) $$ [evs last Hcons]
  · iexists [], slice.nil, _, 0, W64 0
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; refine ⟨Cur_zero, fun e h => by simp at h⟩
    iintro !> %i %e %h
    simp at h
  wp_for IH
  wp_apply (wp_respChan_receive wch γ Ok m c) $$ [Hcons]
    as %v %ok H
  · iframe #; iframe
  cases ok
  · -- the channel closed
    simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iintro %h; cases h
  simp only [↓reduceIte]
  imod H with ⟨%r, %c', #Hr, #Hok, Hcons⟩
  (try wp_auto)
  ihave #Hcse := Hce c c' v r $$ Hok
  wp_apply wp_Err wresp_ptr v (DFrac.own 1) $$ [$wresp $Hcse] as %err ⟨wresp, %Herr, -⟩
  cases err with
  | ok e =>
    -- an error response
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iintro %h; cases h
  | nil =>
  have hnw : ¬ watchErr v := by
    have h := Herr.1 rfl
    unfold watchErr
    rintro (h' | h' | h') <;> simp_all
  imod (Hresp evs0.length c c' v r hnw Hc.1) $$ HA Hok
    with ⟨%Hcur', #Hevf⟩
  iunfold respAt at Hr
  icases Hr with ⟨#Hevs, -, -⟩
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
  ihave %Hlsl := ownSlice_len $$ Hls
  (try wp_auto)
  ihave IJ : (∃ (j : w64) (e0 : Loc) (sl' : GoSlice) (lv' : w64) (ws : List wev),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "evs" ∷ evs_ptr ↦ sl' ∗ "last" ∷ last_ptr ↦ lv' ∗
      "Hs" ∷ sl' ↦* (evs0 ++ ws) ∗ "Hcap" ∷ ownSliceCap wev sl' (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v.Events'.len ∧ ws.length = sint.nat j ∧
        ∀ e, (evs0 ++ ws).getLast? = some e → lv' = e.Rev'⌝ ∗
      "#Hws" ∷ □ ∀ (i : Nat) (w : wev), ⌜ws[i]? = some w⌝ -∗ F (evs0.length + i) w :
      IProp GF) $$ [i e evs last Hs Hcap]
  · iexists W64 0, _, sl, lv, []
    simp only [List.append_nil]
    iframe
    isplitr
    · ipureintro; refine ⟨by word, by word, rfl, Hc.2⟩
    iintro !> %i %w %h
    simp at h
  wp_for IJ
  split
  · rename_i Hif
    have Hif' : sint.Z j < sint.Z v.Events'.len := of_decide_eq_true Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z v.Events'.len := ⟨Hj.1, Hif'⟩
    (try wp_auto)
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem ls (sint.nat j) as ev
    obtain ⟨e, he⟩ : ∃ e, r.events[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact (List.getElem?_eq_some_iff.mp Hev_lookup).1)⟩
    wp_apply wp_load_slice_index v.Events' (sint.Z j) ls DFrac.discard ev Hj.1 $$ [Hls] as -
    · iframe #; ipureintro; exact Hev_lookup
    ihave #Hea := Hev $$ %(sint.nat j) %ev %e %Hev_lookup %he
    ihave #Hf := Hevf $$ %(sint.nat j) %e %he
    iunfold eventAt at Hea
    icases Hea with ⟨%keySl, #Hty, #Hkvf, #Hkey, #HkeyS, #Hmod⟩
    icases Hf with ⟨%kvv, #Hkvv, #Hra⟩
    iunfold kvValAt at Hkvv
    icases Hkvv with ⟨%kSl', %valSl, -, -, -, -, -, #Hvalf, #HvalS, -⟩
    (try wp_auto)
    wp_apply wp_bytes_to_string keySl e.key DFrac.discard $$ [HkeyS] as -
    · iframe #
    (try wp_auto)
    wp_apply wp_bytes_to_string valSl kvv.value DFrac.discard $$ [HvalS] as -
    · iframe #
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, _⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hl1] as %sl2 ⟨Hs, Hcap, -⟩
    (try wp_auto)
    obtain ⟨hlen', hl'⟩ := Hj.2.2
    have hjn : sint.nat j = ws.length := hlen'.symm
    wp_for_post
    iframe
    iexists j + W64 1, _, sl2, e.rev, ws ++ [evWev e kvv.value]
    rw [List.append_assoc]
    iframe
    isplitr
    · ipureintro
      refine ⟨by word, by word, by simp; word, fun e' he' => ?_⟩
      rw [← List.append_assoc, List.getLast?_append] at he'
      simp at he'
      subst he'
      rfl
    iintro !> %i %w %hw
    rcases Nat.lt_or_ge i ws.length with hi | hi
    · rw [List.getElem?_append_left hi] at hw; iapply Hws $$ %i %w %hw
    · rw [List.getElem?_append_right hi] at hw
      have : i - ws.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hw).1; simp at this; omega
      rw [this] at hw; simp at hw; subst hw
      have hi' : i = sint.nat j := by omega
      rw [hi']
      iexact Hra
  · -- the response's events appended
    rename_i Hif
    have Hif' : ¬ sint.Z j < sint.Z v.Events'.len := fun h => Hif (decide_eq_true h)
    obtain ⟨hj0, hjl, hlen', hl'⟩ := Hj
    have hwsl : ws.length = r.events.length := by rw [hlen', ← Hlen]; have := Hlsl.1; word
    ihave %Hsl2 := ownSlice_len $$ Hs
    ihave #Hall : □ ∀ (i : Nat) (w : wev), ⌜(evs0 ++ ws)[i]? = some w⌝ -∗ F i w $$ []
    · iintro !> %i %w %hw
      rcases Nat.lt_or_ge i evs0.length with hi | hi
      · rw [List.getElem?_append_left hi] at hw; iapply Hrevs $$ %i %w %hw
      · rw [List.getElem?_append_right hi] at hw
        ihave H := Hws $$ %(i - evs0.length) %w %hw
        rw [show evs0.length + (i - evs0.length) = i by omega]
        iexact H
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · -- an event at or above `upTo`: done
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iintro -
        iexists evs0 ++ ws
        iframe
        have hne : evs0 ++ ws ≠ [] := by
          intro h; rw [h] at Hsl2; simp at Hsl2; word
        obtain ⟨e, he⟩ : ∃ e, (evs0 ++ ws).getLast? = some e :=
          ⟨_, List.getLast?_eq_some_getLast hne⟩
        isplitr
        · ipureintro
          refine Or.inr ⟨e, he, ?_⟩
          rw [← hl' e he]; word
        iexact Hall
      · (try wp_auto)
        wp_for_post
        iframe
        iexists evs0 ++ ws, sl', lv', m + 1, c'
        iframe
        isplitr
        · ipureintro
          exact ⟨by rw [List.length_append, hwsl]; exact Hcur', hl'⟩
        iexact Hall
    · (try wp_auto)
      wp_for_post
      iframe
      iexists evs0 ++ ws, sl', lv', m + 1, c'
      iframe
      isplitr
      · ipureintro
        exact ⟨by rw [List.length_append, hwsl]; exact Hcur', hl'⟩
      iexact Hall

end proof

end common
end EtcdGrove
end Perennial
