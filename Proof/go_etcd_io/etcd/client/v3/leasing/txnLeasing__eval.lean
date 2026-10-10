/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__eval.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__eval
public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__NotifyOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__evalCmp
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__evalOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.copyHeader
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingCommitLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.eval.wp_proof (hgather : gatherOps.spec (GF := GF) (hG := hG))
    (hnotify : leaseCache.NotifyOps.spec (GF := GF) (hG := hG))
    (hcmp : leaseCache.evalCmp.spec (GF := GF) (hG := hG))
    (hops : leaseCache.evalOps.spec (GF := GF) (hG := hG))
    (hcopy : copyHeader.spec (GF := GF) (hG := hG)) :
    txnLeasing.eval.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b
  wp_start as ⟨Htxn, Hrd, %Hbnd⟩
  icases ownTxnLeasing_acc $$ Htxn with ⟨%csl, %tsl, %esl, %tops, %eops, Hl, Hc, Hcs, Hts, Hes,
    #⟨Hlkv, Hctx, Hcmps, Hthen, Helse⟩, %Hops, Hback⟩
  obtain ⟨Ht, He⟩ := Hops
  wp_apply wp_with_defer as %defer defer
  ihave ⟨%tvs, #Htvs, Htl⟩ := opsAt_gather tsl b.thenOs tops Ht $$ Hthen
  wp_apply hgather $$ [$Htvs $Htl] as %tr ⟨Htr, %Htr4⟩
  ihave ⟨%evs, #Hevs, Hel⟩ := opsAt_gather esl b.elseOs eops He $$ Helse
  wp_apply hgather $$ [$Hevs $Hel] as %er ⟨Her, %Her4⟩
  simp only [leavesL_leaves] at Htr4 Her4 ⊢
  unfold opsOwn
  icases Htr with ⟨%trv, #Htrv, Htrcap, %Htrl, #Htrall⟩
  icases Her with ⟨%erv, #Herv, Hercap, %Herl, #Herall⟩
  ihave %Htrlen := ownSlice_len _ _ _ $$ Htrv
  ihave %Herlen := ownSlice_len _ _ _ $$ Herv
  have hsum : 0 ≤ sint.Z (tr.len + er.len) := by
    have h1 := Htrlen.1; have h2 := Herlen.1
    rw [Htrl] at h1; rw [Herl] at h2
    have e1 : ((sint.nat tr.len : Nat) : Int) = sint.Z tr.len := Int.toNat_of_nonneg Htrlen.2
    have e2 : ((sint.nat er.len : Nat) : Int) = sint.Z er.len := Int.toNat_of_nonneg Herlen.2
    have : sint.Z tr.len + sint.Z er.len < 2 ^ 63 := by
      have := Htrlen.2; have := Herlen.2
      omega
    word
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Op) (W64 0) (tr.len + er.len)
    ⟨by word, by word⟩ as %ops ⟨Hops, Hopscap, -⟩
  simp only [List.replicate_zero]
  wp_apply wp_slice_append $$ [$Hops $Hopscap $Htrv] as %ops1 ⟨Hops1, Hops1cap, -⟩
  wp_apply wp_slice_append $$ [$Hops1 $Hops1cap $Herv] as %ops2 ⟨Hops2, Hops2cap, -⟩
  ipersist Hops2
  simp only [List.nil_append]
  ihave #Hopsat := opsAt_app ops2 trv erv b.thenOs b.elseOs Htrl Herl $$ [$Hops2 $Htrall $Herall]
  ihave #Hcache := isLeasingKV_cache $$ Hlkv
  wp_apply hnotify $$ [$Hcache $Hrd $Hopsat] as %chs ⟨Hrd, %cl, Hchs, Hchscap, #Hwcs⟩
  ihave %Hchslen := ownSlice_len _ _ _ $$ Hchs
  ihave IH : iprop(∃ (n : w64) (c0 : GoChan),
      "i" ∷ i_ptr ↦ n ∗ "ch" ∷ ch_ptr ↦ c0 ∗ "Hchs" ∷ chs ↦* cl ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cl.length : Int)⌝) $$ [i ch Hchs]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < cl.length := by word
    obtain ⟨c, Hci⟩ : ∃ c, cl[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chs.len := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self, ↓reduceIte]
    wp_apply wp_load_slice_index chs (sint.Z n) cl (DFrac.own 1) c Hn.1 $$ [Hchs] as Hchs
    · iframe; ipureintro; exact Hci
    ihave #Hwc := (BigSepL.bigSepL_lookup (Φ := fun _ c => waitcOk (GF := GF) c) Hci) $$ Hwcs
    ihave #Hctx' := Hctx
    unfold context.isContext context.isContextDef
    iNamed Hctx'
    wp_apply HDone as %ch1 %γ1 #Hdone
    unfold waitcOk
    icases Hwc with ⟨%γw, #Hbw⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, c, γw
      isplit
      · ipureintro; rfl
      isplit
      · iapply ownBroadcastChan_is_chan $$ Hbw
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hbw
      iintro ⟨-, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, c
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply context.isContextDone_is_chan $$ Hdone
      iapply context.isContextDone_receive _ _ _ _ $$ Hdone
      iintro -
      wp_auto
      ihave #HErrU := HErr $$ %Broadcast.Unknown
      wp_apply HErrU as %err -
      wp_for_post
      iapply HΦ
      isplitl [Hl Hc Hcs Hts Hes Hback]
      · iapply Hback $$ Hl Hc Hcs Hts Hes
      iframe
      ileft; ipureintro; rfl
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    unfold lkvReader leaseCacheReader
    wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
    icases leaseCacheInv_open $$ HP with ⟨%st, Hown, HX, Hinst, #Hfacts, %Hwf, Hclose⟩
    ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
    unfold lcPeek
    icases Hpeek $$ %st %_ HX with ⟨HX, #HQr⟩
    wp_apply hcmp $$ [$Hown $Hcmps] as %succ %ok ⟨Hown, %Hcmpr⟩
    · ipureintro; exact Hwf
    rw [lcOwn_def]
    icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
    cases ok with
    | false =>
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
        as Hrd
      · inext
        iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
        iframe
        iframe #
      iapply HΦ
      isplitl [Hl Hc Hcs Hts Hes Hback]
      · iapply Hback $$ Hl Hc Hcs Hts Hes
      iframe
      ileft; ipureintro; rfl
    | true =>
    by_cases hh : st.header = null
    · rw [hh]
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
        as Hrd
      · inext
        iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
        iframe
        iframe #
      iapply HΦ
      isplitl [Hl Hc Hcs Hts Hes Hback]
      · iapply Hback $$ Hl Hc Hcs Hts Hes
      iframe
      ileft; ipureintro; rfl
    · wp_auto
      rw [decide_eq_false hh]
      cases succ with
      | true =>
        wp_auto
        wp_apply hops $$ [Hentries Hemap Hrv Hrmap Hhdr Hents $Hthen] as %rs %ok2 ⟨Hown, %Hok2, Hres⟩
        · rw [lcOwn_def]; iframe; iframe #; ipureintro; exact Hwf
        rw [lcOwn_def]
        icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk', Hents, #Hfrozen'⟩
        icases Hres with (%Hno | ⟨%Hyes, %ps, Hrs, %Hpsl, Hps⟩)
        · obtain ⟨rfl, rfl⟩ := Hno
          wp_auto
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
            iframe
            iframe #
          iapply HΦ
          isplitl [Hl Hc Hcs Hts Hes Hback]
          · iapply Hback $$ Hl Hc Hcs Hts Hes
          iframe
          ileft; ipureintro; rfl
        · subst Hyes
          wp_auto
          wp_apply hcopy $$ [$HhdrOk] as %h' Hh'
          icases Hh' with (%Hcn | ⟨-, #Hh'⟩)
          · exact absurd Hcn.1 hh
          wp_alloc r as Hr
          ihave %Hrnn := typedPointsto_not_null $$ Hr
          iStructNamed Hr
          wp_auto
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
            iframe
            iframe #
          iapply HΦ
          isplitl [Hl Hc Hcs Hts Hes Hback]
          · iapply Hback $$ Hl Hc Hcs Hts Hes
          iframe Hrd
          iright
          isplitr
          · ipureintro; exact ⟨Hrnn, rfl⟩
          unfold evalResult
          iexists st, true, h', rs, ps
          iframe
          iframe #
          ipureintro
          refine ⟨Hcmpr.symm, hh, Hok2.symm, ?_⟩
          simpa using Hpsl
      | false =>
        wp_auto
        wp_apply hops $$ [Hentries Hemap Hrv Hrmap Hhdr Hents $Helse] as %rs %ok2 ⟨Hown, %Hok2, Hres⟩
        · rw [lcOwn_def]; iframe; iframe #; ipureintro; exact Hwf
        rw [lcOwn_def]
        icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk', Hents, #Hfrozen'⟩
        icases Hres with (%Hno | ⟨%Hyes, %ps, Hrs, %Hpsl, Hps⟩)
        · obtain ⟨rfl, rfl⟩ := Hno
          wp_auto
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
            iframe
            iframe #
          iapply HΦ
          isplitl [Hl Hc Hcs Hts Hes Hback]
          · iapply Hback $$ Hl Hc Hcs Hts Hes
          iframe
          ileft; ipureintro; rfl
        · subst Hyes
          wp_auto
          wp_apply hcopy $$ [$HhdrOk] as %h' Hh'
          icases Hh' with (%Hcn | ⟨-, #Hh'⟩)
          · exact absurd Hcn.1 hh
          wp_alloc r as Hr
          ihave %Hrnn := typedPointsto_not_null $$ Hr
          iStructNamed Hr
          wp_auto
          wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hclose Hentries Hemap Hrv Hrmap Hhdr Hents HX Hinst]
            as Hrd
          · inext
            iapply Hclose $$ [Hentries Hemap Hrv Hrmap Hhdr Hents] HX Hinst
            iframe
            iframe #
          iapply HΦ
          isplitl [Hl Hc Hcs Hts Hes Hback]
          · iapply Hback $$ Hl Hc Hcs Hts Hes
          iframe Hrd
          iright
          isplitr
          · ipureintro; exact ⟨Hrnn, rfl⟩
          unfold evalResult
          iexists st, false, h', rs, ps
          iframe
          iframe #
          ipureintro
          refine ⟨Hcmpr.symm, hh, Hok2.symm, ?_⟩
          simpa using Hpsl

end proof

end leasing
end EtcdGrove
end Perennial
