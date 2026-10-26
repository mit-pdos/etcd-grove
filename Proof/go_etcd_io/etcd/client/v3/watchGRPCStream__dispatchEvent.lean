/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__dispatchEvent.lean` (the watch slice's
unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__dispatchEvent
public import Spec.go_etcd_io.etcd.client.v3.ensureWatchHeader
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__IsProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__broadcastResponse
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__unicastResponse

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
/-- The model of the `WatchResponse` `dispatchEvent` makes (`IsProgressNotify`'s view). -/
def dispModel (mm : v3rpc.WatchRespM) (es : List EvModel) : RespModel :=
  { events := es, compactRev := mm.compactRev, canceled := mm.canceled, created := mm.created,
    hdrRev := mm.hdr.revision }

/-- `dispatchEvent` broadcasts exactly the progress notifications of id `-1`. -/
theorem isBroadcast_iff (mm : v3rpc.WatchRespM) (es : List EvModel)
    (hl : es.length = mm.evs.length) :
    isBroadcast mm ↔ (dispModel mm es).isProgressNotify = true ∧ mm.watchId = W64 (-1) := by
  have he : es = [] ↔ mm.evs = [] := by
    rw [← List.length_eq_zero_iff, hl, List.length_eq_zero_iff]
  unfold isBroadcast RespModel.isProgressNotify dispModel
  simp only [List.isEmpty_iff, he, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  simp only [and_assoc, ne_eq]

theorem watchGRPCStream.dispatchEvent.wp_proof
    (wp_ensureWatchHeader : ensureWatchHeader.spec (GF := GF) (hG := hG))
    (wp_IsProgressNotify : WatchResponse.IsProgressNotify.spec (GF := GF) (hG := hG))
    (wp_broadcastResponse : watchGRPCStream.broadcastResponse.spec (GF := GF) (hG := hG))
    (wp_unicastResponse : watchGRPCStream.unicastResponse.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.dispatchEvent.spec (GF := GF) (hG := hG) := by
  intro V wgs p dq mm h sl es m M dq1 dq2 Pf Sf Df γend n Ψ
  wp_start as ⟨Hf, #Hevs, %Hlen, #Hhdr, Hsub, Hmap, Hauth, Hcaps⟩
  iunfold respFields at Hf
  icases Hf with ⟨%Hhn, Hh, Hid, Hcr, Hca, Hcomp, Hrs, Hfr, Hev⟩
  (try wp_auto)
  wp_apply wp_ensureWatchHeader h as %h' ⟨%Hh'n, Hh'⟩
  icases Hh' with (%Hh' | ⟨%Hh', -⟩)
  · obtain ⟨-, rfl⟩ := Hh'
    (try wp_auto)
    ipersist «$r0»
    ihave #HΨ : («$r0_ptr» ↦□ wrOf mm h' sl : IProp GF) $$ []
    · unfold wrOf; iexact «$r0»
    have Hbr := isBroadcast_iff mm es Hlen
    wp_apply wp_IsProgressNotify «$r0_ptr» (wrOf mm h' sl) (dispModel mm es) DFrac.discard
      $$ [$HΨ] as -
    · simp only [wrOf, dispModel]
      isplitr
      · iexact Hevs
      isplitr
      · iintro %He
        iapply Hhdr
        ipureintro
        rw [← List.length_eq_zero_iff, ← Hlen, List.length_eq_zero_iff]; exact He
      ipureintro; simp
    cases hpn : (dispModel mm es).isProgressNotify
    · have Hnb : ¬ isBroadcast mm := fun h => by simp [(Hbr.1 h).1] at hpn
      (try wp_auto)
      simp only [decide_eq_false Hnb, Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      cases hM : M !! mm.watchId with
      | none =>
        simp only []
        wp_apply wp_unicastResponse V wgs «$r0_ptr» mm.watchId m M dq1 dq2 Pf Sf Df γend n $$ [$Hsub $Hmap $Hauth]
          as %b ⟨Hsub, Hmap, Hauth, Hb⟩
        · rw [hM]; itrivial
        rw [hM]
        iapply HΦ
        isplitl [Hh Hid Hcr Hca Hcomp Hrs Hfr Hev]
        · iunfold respFields; iframe; ipureintro; exact Hhn
        iframe
      | some ws =>
        simp only []
        icases Hcaps with ⟨%HPws, Hcap⟩
        iunfold sendCap at Hcap
        icases Hcap with ⟨#Hws, Hprod, Hf, Hdc⟩
        ihave Hel := Hf $$ %«$r0_ptr» HΨ
        wp_apply wp_unicastResponse V wgs «$r0_ptr» mm.watchId m M dq1 dq2 Pf Sf Df γend n
          $$ [$Hsub $Hmap $Hauth Hprod Hel Hdc] as %b ⟨Hsub, Hmap, Hauth, Hb⟩
        · rw [hM]
          iframe
          isplitr
          · ipureintro; exact HPws
          iunfold sendCap1
          iframe
          iexact Hws
        rw [hM]
        iapply HΦ
        isplitl [Hh Hid Hcr Hca Hcomp Hrs Hfr Hev]
        · iunfold respFields; iframe; ipureintro; exact Hhn
        iframe
    · (try wp_auto)
      wp_if_destruct
      · have Hb : isBroadcast mm := Hbr.2 ⟨hpn, by assumption⟩
        simp only [decide_eq_true Hb, ↓reduceIte]
        (try wp_auto)
        wp_apply wp_broadcastResponse V wgs «$r0_ptr» m M dq1 dq2 Pf Sf Df γend n $$ [$Hsub $Hmap $Hauth Hcaps]
          as ⟨Hsub, Hmap, Hauth, Hb⟩
        · iapply BigSepM.bigSepM_impl $$ Hcaps
          imodintro
          iintro %k %ws %_ ⟨%HPws, Hcap⟩
          iunfold sendCap at Hcap
          icases Hcap with ⟨#Hws, Hprod, Hf, Hdc⟩
          ihave Hel := Hf $$ %«$r0_ptr» HΨ
          iframe
          isplitr
          · ipureintro; exact HPws
          iunfold sendCap1
          iframe
          iexact Hws
        iapply HΦ
        isplitl [Hh Hid Hcr Hca Hcomp Hrs Hfr Hev]
        · iunfold respFields; iframe; ipureintro; exact Hhn
        iframe
        ipureintro; rfl
      · have Hnb : ¬ isBroadcast mm := fun h => by simp_all
        simp only [decide_eq_false Hnb, Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        cases hM : M !! mm.watchId with
        | none =>
          simp only []
          wp_apply wp_unicastResponse V wgs «$r0_ptr» mm.watchId m M dq1 dq2 Pf Sf Df γend n $$ [$Hsub $Hmap $Hauth]
            as %b ⟨Hsub, Hmap, Hauth, Hb⟩
          · rw [hM]; itrivial
          rw [hM]
          iapply HΦ
          isplitl [Hh Hid Hcr Hca Hcomp Hrs Hfr Hev]
          · iunfold respFields; iframe; ipureintro; exact Hhn
          iframe
        | some ws =>
          simp only []
          icases Hcaps with ⟨%HPws, Hcap⟩
          iunfold sendCap at Hcap
          icases Hcap with ⟨#Hws, Hprod, Hf, Hdc⟩
          ihave Hel := Hf $$ %«$r0_ptr» HΨ
          wp_apply wp_unicastResponse V wgs «$r0_ptr» mm.watchId m M dq1 dq2 Pf Sf Df γend n
            $$ [$Hsub $Hmap $Hauth Hprod Hel Hdc] as %b ⟨Hsub, Hmap, Hauth, Hb⟩
          · rw [hM]
            iframe
            isplitr
            · ipureintro; exact HPws
            iunfold sendCap1
            iframe
            iexact Hws
          rw [hM]
          iapply HΦ
          isplitl [Hh Hid Hcr Hca Hcomp Hrs Hfr Hev]
          · iunfold respFields; iframe; ipureintro; exact Hhn
          iframe
  · exact absurd Hh' Hhn

end proof

end EtcdGrove
end Perennial
