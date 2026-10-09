/-
Proof of `Spec/watcher__enqueueResponse.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.watcher__enqueueResponse
import EtcdGrove.Cache.Spec.WatchResponse__IsProgressNotify

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem watcher.enqueueResponse.wp_proof
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG)) :
    watcher.enqueueResponse.spec (GF := GF) (hG := hG) := by
  intro w γ pred sent resp r
  wp_start as ⟨#Hw, Hopen, #Hresp⟩
  ihave #Hw0 := Hw
  iNamed Hw
  wp_auto
  wp_apply wp_IsProgressNotify resp_ptr resp r (DFrac.own 1) $$ [$resp $Hresp] as resp
  ipersist w
  -- the filter statement: it falls through with the response to send, or returns `true`
  wp_join (Q := fun v => iprop(
      (⌜v = executeVal⌝ ∗ ∃ (resp' : go_etcd_io.etcd.client.v3.WatchResponse) (r' : RespModel),
        "resp" ∷ resp_ptr ↦ resp' ∗ "#Hresp'" ∷ respAt resp' r' ∗
        "%Hr'" ∷ ⌜filterResp pred r = some r' ∧ resp'.Header' = resp.Header'⌝) ∨
      (⌜v = returnVal #true⌝ ∗ ⌜filterResp pred r = none⌝))) at next with [resp]
  · cases pred with
    | none =>
      unfold keyPredOk
      icases Hpred with %Hf
      subst Hf
      cases hpn : r.isProgressNotify <;> wp_auto <;>
        (ileft; iframe; iframe #; ipureintro; exact ⟨rfl, rfl, rfl⟩)
    | some p =>
      unfold keyPredOk
      icases Hpred with ⟨%Hf, #Hf⟩
      cases hpn : r.isProgressNotify
      · ihave #Hresp2 := Hresp
        unfold respAt eventsAt
        icases Hresp2 with ⟨⟨%ls, #Hls, %Hlslen, #Hevs⟩, #Hhdr, %Hflds⟩
        ihave %Hsl := ownSlice_len _ _ _ $$ Hls
        wp_auto
        rw [decide_eq_false Hf]
        wp_auto
        wp_apply wp_slice_make3 (V := Loc) (W64 0) resp.Events'.len (by word) as %fsl0 ⟨Hf0, Hfcap0, %Hfcap0⟩
        ihave HI : (∃ (i : w64) (fsl : GoSlice),
            "i" ∷ i_ptr ↦ i ∗ "filtered" ∷ filtered_ptr ↦ fsl ∗
            "Hfl" ∷ fsl ↦* ((filterPairs p (ls.take (sint.nat i)) (r.events.take (sint.nat i))).map
              Prod.fst) ∗
            "Hfcap" ∷ ownSliceCap Loc fsl (DFrac.own 1) ∗
            "event" ∷ (∃ ev : Loc, event_ptr ↦ ev) ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z resp.Events'.len⌝ : IProp GF)
          $$ [i filtered Hf0 Hfcap0 event]
        · iexists W64 0, fsl0
          simp only [named, filterPairs, sint.nat]
          iframe
          ipureintro; word
        wp_for HI
        wp_if_destruct
        · -- `i < len(events)`: the `i`-th event
          have hi : sint.nat i < ls.length := by rw [Hsl.1]; word
          list_elem ls (sint.nat i) as ev
          list_elem r.events (sint.nat i) as e
          icases event with ⟨%ev0, event⟩
          ihave #Hev := Hevs $$ %(sint.nat i) %ev %e %Hev_lookup %He_lookup
          unfold eventAt
          icases Hev with ⟨%keySl, #HType, #HKv, #HKey, #HkeySl, #HMod⟩
          simp only [show (0 ≤ sint.Z i ∧ sint.Z i < sint.Z resp.Events'.len) from ⟨Hi.1, Hif⟩]
          wp_apply wp_load_slice_index resp.Events' (sint.Z i) ls DFrac.discard ev (by word) $$ [] as -
          · iframe #; ipureintro; rw [show (sint.Z i).toNat = sint.nat i from rfl]; exact Hev_lookup
          unfold keyPredSpec
          wp_apply Hf $$ %keySl %e.key []
          · iexact HkeySl
          have hsucc : sint.nat (i + W64 1) = sint.nat i + 1 := by word
          have Hfp := filterPairs_take_succ p ls r.events (sint.nat i) ev e Hev_lookup He_lookup
          cases hp : p e.key
          · -- not selected
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, fsl
            simp only [named]
            rw [hsucc, Hfp, hp]
            simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
            iframe
            ipureintro; word
          · -- selected: `filtered = append(filtered, event)`
            wp_auto
            wp_apply wp_slice_literal (V := Loc) [ev]
            isplitr
            · ipureintro; rfl
            iintro %sl2 ⟨Hsl2, -⟩
            wp_auto
            wp_apply wp_slice_append $$ [Hfl Hfcap Hsl2] with %sl' ⟨Hfl, Hfcap, -⟩
            · iframe
            wp_for_post
            iframe
            iexists i + W64 1, sl'
            simp only [named]
            rw [hsucc, Hfp, hp]
            simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
            iframe
            ipureintro; word
        · -- the loop is done: `filtered` holds the selected events
          have hlen : sint.nat i = ls.length := by rw [Hsl.1]; word
          rw [hlen, List.take_of_length_le (Nat.le_refl _),
            List.take_of_length_le (Nat.le_of_eq Hlslen.symm)]
          ihave %Hflen := ownSlice_len _ _ _ $$ Hfl
          ipersist Hfl
          have Hsnd := filterPairs_snd p ls r.events Hlslen
          wp_if_destruct
          · -- nothing selected: `return true`
            iright
            ipureintro
            refine ⟨by first | rfl | trivial, ?_⟩
            have h0 : (filterPairs p ls r.events).length = 0 := by
              simp only [List.length_map] at Hflen; word
            have : r.events.filter (fun e => p e.key) = [] := by
              rw [← Hsnd, List.eq_nil_of_length_eq_zero h0]; rfl
            simp [filterResp, hpn, this]
          · -- send the filtered response
            have hne : r.events.filter (fun e => p e.key) ≠ [] := by
              intro h
              rw [← Hsnd] at h
              have := congrArg List.length h
              simp only [List.length_map, List.length_nil] at this Hflen
              apply Hif; word
            ileft
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _, { r with events := r.events.filter (fun e => p e.key) }
            iframe
            simp only [named]
            try unfold respAt eventsAt
            isplitl
            · isplitl
              · iexists _
                iframe Hfl
                isplitr
                · ipureintro; rw [← Hsnd]; simp
                imodintro
                iintro %j %ev' %e' %Hj1 %Hj2
                rw [← Hsnd] at Hj2
                obtain ⟨k, hk1, hk2⟩ := filterPairs_get p ls r.events j ev' e' Hj1 Hj2
                iapply Hevs $$ %k %ev' %e' %hk1 %hk2
              isplitl
              · iexact Hhdr
              ipureintro; exact Hflds
            ipureintro
            refine ⟨?_, trivial⟩
            simp [filterResp, hpn, hne]
      · wp_auto
        ileft; iframe; iframe #; ipureintro
        simp [filterResp, hpn]
  iintro HQ
  icases HQ with (⟨%Hv, %resp', %r', resp, #Hresp', %Hr'⟩ | ⟨%Hv, %Hnone⟩)
  rotate_left
  · -- the filter dropped every event: nothing sent, reported delivered
    subst Hv
    wp_auto
    iapply HΦ
    iexists sent
    iframe
    ipureintro
    simp [enqueueResult, Hnone]
  subst Hv
  obtain ⟨Hfr, Hhdr⟩ := Hr'
  wp_auto
  -- a nil header is replaced by an empty one; either way the response has a non-nil header
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (resp'' : go_etcd_io.etcd.client.v3.WatchResponse),
        "resp" ∷ resp_ptr ↦ resp'' ∗ "#Hsent" ∷ respSent resp'' r')) at next with [resp]
  · iapply wp_fupd
    wp_if_destruct
    · -- nil header: an empty one, `Revision = 0` as the model's `hdrRev`
      ihave %Hhdr0 : ⌜r'.hdrRev = W64 0⌝ $$ []
      · unfold respAt hdrAt
        icases Hresp' with ⟨-, (%Hh | ⟨%Hh, -⟩), -⟩
        · ipureintro; exact Hh.2
        · exact absurd Hif Hh
      ihave %Hhnn := typedPointsto_not_null $$ «$r0»
      iStructNamed «$r0»
      ipersist Revision
      imodintro
      unfold respAt
      icases Hresp' with ⟨#Hev, -, %Hp⟩
      iframe
      simp only [named]
      unfold respSent respAt hdrAt
      dsimp only
      isplitr
      · isplitr
        · iexact Hev
        isplitr
        · iright
          isplitr
          · ipureintro; exact Hhnn
          rw [Hhdr0, show (zero_val go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader).Revision' =
            W64 0 from rfl]
          iexact Revision
        ipureintro; exact Hp
      ipureintro; exact Hhnn
    · imodintro
      iframe
      unfold respSent
      simp only [named]
      isplitr
      · iexact Hresp'
      ipureintro; exact Hif
  iintro ⟨%Hv, %resp'', resp, #Hsent⟩
  subst Hv
  wp_auto
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply wp_watcher_send w ch γ pred sent resp'' r' _ _ _ $$ Hw0 HrespCh Hopen Hsent
  isplit
  · iintro Hopen
    wp_auto
    iapply HΦ
    iexists sent ++ [r']
    iframe
    ipureintro
    simp [enqueueResult, Hfr]
  · iintro Hopen
    wp_auto
    iapply HΦ
    iexists sent
    iframe
    ipureintro
    simp [enqueueResult, Hfr]

end proof

end EtcdGrove
end Perennial
