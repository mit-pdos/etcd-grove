/-
Proof of `Spec/demux__broadcastLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastLocked
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastProgressLocked
public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastEventsLocked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.broadcastLocked.wp_proof
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_broadcastProgressLocked : demux.broadcastProgressLocked.spec (GF := GF) (hG := hG))
    (wp_broadcastEventsLocked : demux.broadcastEventsLocked.spec (GF := GF) (hG := hG)) :
    demux.broadcastLocked.spec (GF := GF) (hG := hG) := by
  intro d γd cap C c k regs views resp r
  wp_start as ⟨Hl, #Hresp, % ⟨Hinv, Hpre⟩⟩
  ihave #Hresp' := Hresp
  iunfold respAt at Hresp'
  icases Hresp' with ⟨#HevsAt, #Hhdr, %-⟩
  wp_auto
  wp_apply wp_IsProgressNotify resp_ptr resp r (DFrac.own 1) $$ [resp] as resp
  · iframe resp; iexact Hresp
  unfold BroadcastPre at Hpre
  cases hpn : r.isProgressNotify
  · simp only [hpn, Bool.false_eq_true, ↓reduceIte] at Hpre
    ihave #HevsAt' := HevsAt
    iunfold eventsAt at HevsAt'
    icases HevsAt' with ⟨%ls, #Hls, %Hlslen, #-⟩
    ihave %Hsllen := ownSlice_len _ _ _ $$ Hls
    wp_auto
    by_cases he : r.events = []
    · have Hlen0 : resp.Events'.len = W64 0 := by
        have h0 : ls.length = 0 := by rw [Hlslen, he]; rfl
        have h1 := Hsllen.1; have h2 := Hsllen.2
        word
      simp only [he, ↓reduceIte] at Hpre
      subst Hpre
      simp only [Hlen0, _root_.decide_true, Bool.not_true, Bool.true_eq_false, _root_.decide_false]
      wp_auto
      iapply HΦ
      iexists views
      iexact Hl
    · have Hlen0 : resp.Events'.len ≠ W64 0 := by
        intro h; apply he
        apply List.eq_nil_of_length_eq_zero
        have h1 := Hsllen.1
        rw [h] at h1
        have : sint.nat (W64 0) = 0 := by word
        omega
      simp only [he, ↓reduceIte] at Hpre
      simp only [Hlen0, _root_.decide_false, Bool.not_false, _root_.decide_true]
      wp_auto
      wp_apply wp_broadcastEventsLocked d γd cap C c k regs views resp.Events' r.events $$ [Hl]
        as ⟨%views', Hl⟩
      · iframe Hl; iframe HevsAt; ipureintro; exact ⟨Hinv, he, Hpre.1, Hpre.2⟩
      iapply HΦ
      iexists views'
      iexact Hl
  · simp only [hpn, ↓reduceIte] at Hpre
    obtain ⟨rfl, Hrev⟩ := Hpre
    simp only [_root_.decide_true]
    have hhr : r.hdrRev ≠ W64 0 := by
      simp only [RespModel.isProgressNotify, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at hpn
      exact hpn.2
    iunfold hdrAt at Hhdr
    icases Hhdr with (%Hnil | ⟨%Hnn, #Hh⟩)
    · exact absurd Hnil.2 hhr
    wp_auto
    wp_apply wp_broadcastProgressLocked d γd cap C c regs views r.hdrRev $$ [Hl] as ⟨%views', Hl⟩
    · iframe Hl; ipureintro; exact ⟨Hinv, Hrev, hhr⟩
    iapply HΦ
    iexists views'
    iexact Hl

end proof

end EtcdGrove
end Perennial
