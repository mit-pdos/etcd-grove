/- Lean-first (no Rocq counterpart). The proof of `awaitProgress` (2026-11-03): `collect`'s loop
over the cache watch's channel (`wp_cacheWatch_receive`; each response's events by `log_ck`, the
inner loop appending them), ending at a progress notification, whose revision is not past the
events (`log_ck_progress`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.cachekv.awaitProgress
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.collect

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.cachekv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

set_option maxHeartbeats 800000 in
theorem awaitProgress.wp_proof
    (wp_IPN : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG)) :
    awaitProgress.spec (GF := GF) (hG := hG) := by
  intro CS VS γk P wch γ rangeEnd upTo sl evs rs hW hpk hkeys hc0 hl0
  wp_start as ⟨#Hw, Hcons, #Hinv, Hs0, Hcap0, Hcok⟩
  icases common.collectOk_elim _ _ _ _ $$ Hcok with ⟨%Hcp, #Hrevs0⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  ihave IH : (∃ (evs0 : List cev) (sl : GoSlice) (rs : List RespModel),
      "evs" ∷ evs_ptr ↦ sl ∗ "Hs" ∷ sl ↦* evs0 ∗
      "Hcap" ∷ ownSliceCap cev sl (DFrac.own 1) ∗
      "Hcons" ∷ cacheWatchConsumer γ (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) rs ∗
      "%Hc" ∷ ⌜(∀ r ∈ rs, r.canceled = false) ∧ evs0.length = (eventsOf rs).length ∧
        (upTo = W64 0 ∨ sint.Z upTo ≤ 1 + evs0.length) ∧ evs0.length + 1 < 2 ^ 63 ∧
        ∀ (i : Nat) (e : cev), evs0[i]? = some e →
          e.Put' = true ∧ sint.Z e.Rev' = 2 + i ∧ (e.Key', e.Val') ∈ P⌝ ∗
      "#Hrevs" ∷ □ ∀ (i : Nat) (e : cev), ⌜evs0[i]? = some e⌝ -∗
        common.kmRevAt γk (2 + i) e.Key' e.Val' :
      IProp GF) $$ [evs Hs0 Hcap0 Hcons]
  · iexists evs, sl, rs
    iframe
    iframe Hrevs0
    ipureintro
    exact ⟨hc0, hl0, Hcp.1, Hcp.2.1, Hcp.2.2⟩
  wp_for IH
  wp_apply (wp_cacheWatch_receive (EM := client.etcdModelOfKV γk) wch γ
      (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
      (some (keyPredForRange ckPfx rangeEnd)) (W64 2) rs) $$ [Hcons] as %v %ok H
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
  icases H with ⟨%r, #Hr, Hcons⟩
  iunfold respAt at Hr
  icases Hr with ⟨#Hevs, #Hhdr, %Hrf⟩
  (try wp_auto)
  -- a cancel (`Canceled`, or a compaction's revision): the watch ended
  cases hcv : v.Canceled'
  case true =>
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iintro %h; cases h
  (try wp_auto)
  wp_if_destruct
  rotate_left
  · (try wp_auto)
    wp_for_post
    iapply HΦ
    iintro %h; cases h
  have hcan : r.canceled = false := by rw [← Hrf.2.1, hcv]
  ihave ⟨Hcons, #Hlog⟩ := cacheWatchConsumer_log γ _ _ _ (rs ++ [r]) $$ Hcons
  have hc' : ∀ r' ∈ rs ++ [r], r'.canceled = false := by
    intro r' hr'
    rcases List.mem_append.mp hr' with h | h
    · exact Hc.1 r' h
    · simp at h; rw [h]; exact hcan
  ihave #Hlog' : cacheWatchLog (etcdStepCert (EM := client.etcdModelOfKV γk) ckPfx)
      (some (keyPredForRange ckPfx rangeEnd)) (W64 2) (rs ++ [r]) $$ []
  · icases Hlog with (%h | #H)
    · simp at h
    · iexact H
  -- `wresp.IsProgressNotify()`
  wp_apply (wp_IPN wresp_ptr v r (DFrac.own 1)) $$ [wresp] as wresp
  · iframe; iframe #
    ipureintro; exact ⟨fun _ => trivial, Hrf⟩
  cases hpn : r.isProgressNotify
  · -- not a progress notification: append its events
    try simp only [Bool.false_eq_true, ↓reduceIte]
    imod log_ck γk P hW hpk rangeEnd hkeys (rs ++ [r]) hc' $$ Hinv Hlog' with #Hall
    ihave #Hevf : □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        evFact γk P (2 + evs0.length + j) e $$ []
    · iintro !> %j %e %hj
      have he : (eventsOf (rs ++ [r]))[(eventsOf rs).length + j]? = some e := by
        simp only [eventsOf, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil] at hj ⊢
        rw [List.getElem?_append_right (by omega)]
        simpa using hj
      ihave H := Hall $$ %((eventsOf rs).length + j) %e %he
      rw [show 2 + evs0.length + j = 2 + ((eventsOf rs).length + j) by rw [Hc.2.1]; omega]
      iexact H
    iunfold eventsAt at Hevs
    icases Hevs with ⟨%ls, #Hls, %Hlen, #Hev⟩
    ihave %Hlsl := ownSlice_len $$ Hls
    (try wp_auto)
    ihave IJ : (∃ (j : w64) (e0 : Loc) (sl' : GoSlice) (ws : List cev),
        "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "evs" ∷ evs_ptr ↦ sl' ∗
        "Hs" ∷ sl' ↦* (evs0 ++ ws) ∗ "Hcap" ∷ ownSliceCap cev sl' (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z v.Events'.len ∧ ws.length = sint.nat j ∧
          ∀ (i : Nat) (w : cev), ws[i]? = some w →
            w.Put' = true ∧ sint.Z w.Rev' = 2 + evs0.length + i ∧ (w.Key', w.Val') ∈ P⌝ ∗
        "#Hws" ∷ □ ∀ (i : Nat) (w : cev), ⌜ws[i]? = some w⌝ -∗
          common.kmRevAt γk (2 + evs0.length + i) w.Key' w.Val' : IProp GF)
        $$ [i e evs Hs Hcap]
    · iexists W64 0, _, sl, []
      simp only [List.append_nil]
      iframe
      isplitr
      · ipureintro; refine ⟨by word, by word, rfl, fun i w h => by simp at h⟩
      iintro !> %i %w %h
      simp at h
    wp_for IJ
    split
    · rename_i Hif
      have Hif' : sint.Z j < sint.Z v.Events'.len := by simpa using Hif
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
      iunfold evFact at Hf
      iunfold common.evFactR at Hf
      icases Hf with ⟨%Hfe, %val, %kvv, #Hkvv, %Hval, #Hra⟩
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
      obtain ⟨hlen', hws⟩ := Hj.2.2
      have hjn : sint.nat j = ws.length := hlen'.symm
      rw [Hfe.1]
      simp only [_root_.decide_true]
      wp_for_post
      iframe
      iexists j + W64 1, _, sl2,
        ws ++ [{ Rev' := e.rev, Key' := e.key, Val' := kvv.value, Put' := true }]
      rw [List.append_assoc]
      iframe
      isplitr
      · ipureintro
        refine ⟨by word, by word, by simp; word, ?_⟩
        intro i w hw
        rcases Nat.lt_or_ge i ws.length with hi | hi
        · rw [List.getElem?_append_left hi] at hw; exact hws i w hw
        · rw [List.getElem?_append_right hi] at hw
          have : i - ws.length = 0 := by
            have := (List.getElem?_eq_some_iff.mp hw).1; simp at this; omega
          rw [this] at hw; simp at hw; subst hw
          refine ⟨rfl, ?_, ?_⟩
          · rw [Hfe.2]; omega
          · rw [Hval.1]; exact Hval.2
      iintro !> %i %w %hw
      rcases Nat.lt_or_ge i ws.length with hi | hi
      · rw [List.getElem?_append_left hi] at hw; iapply Hws $$ %i %w %hw
      · rw [List.getElem?_append_right hi] at hw
        have : i - ws.length = 0 := by
          have := (List.getElem?_eq_some_iff.mp hw).1; simp at this; omega
        rw [this] at hw; simp at hw; subst hw
        have hi' : i = sint.nat j := by omega
        simp only
        rw [hi', ← Hval.1]
        iexact Hra
    · -- the response's events appended: the next response
      rename_i Hif
      have Hif' : ¬ sint.Z j < sint.Z v.Events'.len := fun h => Hif (by simp [h])
      obtain ⟨hj0, hjl, hlen', hws⟩ := Hj
      have hwsl : ws.length = r.events.length := by rw [hlen', ← Hlen]; have := Hlsl.1; word
      have hlens : (evs0 ++ ws).length = (eventsOf (rs ++ [r])).length := by
        simp only [eventsOf, List.map_append, List.flatten_append, List.length_append,
          List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at Hc ⊢
        rw [Hc.2.1, hwsl]
      ihave %Hsl2 := ownSlice_len $$ Hs
      (try wp_auto)
      wp_for_post
      iframe
      have hall : ∀ (i : Nat) (w : cev), (evs0 ++ ws)[i]? = some w →
          w.Put' = true ∧ sint.Z w.Rev' = 2 + i ∧ (w.Key', w.Val') ∈ P := by
        intro i w hw
        rcases Nat.lt_or_ge i evs0.length with hi | hi
        · rw [List.getElem?_append_left hi] at hw; exact Hc.2.2.2.2 i w hw
        · rw [List.getElem?_append_right hi] at hw
          obtain ⟨h1, h2, h3⟩ := hws _ w hw
          refine ⟨h1, by rw [h2]; push_cast; omega, h3⟩
      have hbound : (evs0 ++ ws).length + 1 < 2 ^ 63 := by
        cases hl : (evs0 ++ ws).length with
        | zero => omega
        | succ k =>
          obtain ⟨w, hw⟩ : ∃ w, (evs0 ++ ws)[k]? = some w :=
            ⟨_, List.getElem?_eq_getElem (by omega)⟩
          have := (hall k w hw).2.1
          have : sint.Z w.Rev' < 2 ^ 63 := by word
          omega
      iexists evs0 ++ ws, sl', rs ++ [r]
      iframe
      isplitr
      · ipureintro
        refine ⟨hc', hlens, ?_, hbound, hall⟩
        rcases Hc.2.2.1 with h | h
        · exact Or.inl h
        · exact Or.inr (by simp only [List.length_append]; omega)
      iintro !> %i %w %hw
      rcases Nat.lt_or_ge i evs0.length with hi | hi
      · rw [List.getElem?_append_left hi] at hw; iapply Hrevs $$ %i %w %hw
      · rw [List.getElem?_append_right hi] at hw
        ihave H := Hws $$ %(i - evs0.length) %w %hw
        rw [show 2 + evs0.length + (i - evs0.length) = 2 + i by omega]
        iexact H
  · -- a progress notification: its revision is not past the events
    try simp only [↓reduceIte]
    have hev : r.events = [] := isProgressNotify_events hpn
    imod log_ck_progress γk P hW hpk rangeEnd hkeys (rs ++ [r]) hc' r
        ⟨by simp, hev⟩ $$ Hinv Hlog' with %Hp
    have hp : sint.Z r.hdrRev ≤ 1 + evs0.length := by
      have : (eventsOf (rs ++ [r])).length = (eventsOf rs).length := by
        simp [eventsOf, hev]
      rw [this] at Hp; rw [Hc.2.1]; exact Hp
    -- the header's revision (the header non-nil: a progress notification's revision is not `0`)
    have h0 : r.hdrRev ≠ W64 0 := by
      unfold RespModel.isProgressNotify at hpn
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hpn
      exact hpn.2
    iunfold hdrAt at Hhdr
    icases Hhdr with (%hn | ⟨%hnn, #Hrev⟩)
    · exact absurd hn.2 h0
    (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    iintro -
    iexists evs0
    iframe
    isplitl []
    · iapply (common.collectOk_intro _ _ _ _ ⟨Hc.2.2.1, Hc.2.2.2.1, Hc.2.2.2.2⟩) $$ Hrevs
    ipureintro; exact hp

end proof

end cachekv
end EtcdGrove
end Perennial
