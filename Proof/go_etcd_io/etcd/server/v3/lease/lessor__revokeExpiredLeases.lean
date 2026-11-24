/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__revokeExpiredLeases.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__revokeExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__findExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell
public import Proof.go_etcd_io.etcd.server.v3.lease.ExpiryLoop
public import Proof.go_etcd_io.etcd.server.v3.lease.SortByExpiry
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.revokeExpiredLeases.wp_proof
    (hPrim : lease.lessor.isPrimary.spec (GF := GF) (hG := hG))
    (hFind : lease.lessor.findExpiredLeases.spec (GF := GF) (hG := hG)) :
    lease.lessor.revokeExpiredLeases.spec (GF := GF) (hG := hG) := by
  intro lp γl GA ri
  wp_start as ⟨#Hinv, #Hcfg, #Hexp, #Hguard, #Hri, Hrd, Htok, Htt, %Htb⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  iunfold lessorCfg at Hcfg
  icases Hcfg with ⟨%mt, %cpp, %cl, %ci, %lg, %rr, -, -, -, -, -, -, -, #Hrr, %Hrrp⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  iunfold lessorRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hns, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr⟩
  iunfold lessorAuth at Ha
  icases Ha with ⟨%γga, %γcl, %γr0, Hga, Hgc, #Hgr⟩
  (try wp_auto)
  wp_apply (hPrim lp dc _) $$ [$Hpkg $Hdc] as Hdc
  ihave #Hstr' := Hstr
  iunfold lessorStopRecv at Hstr'
  icases Hstr' with ⟨%sc, %γts, #Hsc, #Hsr⟩
  iunfold onceRecv at Hsr
  icases Hsr with ⟨%γcs, #Hchs, #Hcis⟩
  iunfold lessorExpiredC at Hexp
  icases Hexp with ⟨%ec, %γec, #Hec, #Hbag⟩
  by_cases hdc : dc = chan.nil
  · -- not primary: nothing found
    simp only [hdc, decide_true, Bool.not_true]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Hga Hgc Hg Hnp Hns Hh Hhq Hcp Hmeta Hbl Hdt
        Hdc Hhist] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe Hlm HM Him HI Hrdf Hg
      isplitl [Hga Hgc]
      · iunfold lessorAuth; iexists γga, γcl, γr0; iframe; iframe #
      isplitr
      · ipureintro; exact HL
      iframe Hsz Hls
      isplitl [Hdc Hnp Hns Hh Hhq Hcp Hmeta Hbl Hdt]
      · iunfold lessorExtra; iexists _, np, h, hx, bl; iframe; iframe #
      iexact Hhist
    (try wp_auto)
    iapply HΦ
    iframe Htok Htt
    iunfold lessorRd; iexact Hrd
  -- primary: the expired leases, the notifier taken out of its cell for the search
  simp only [hdc, decide_false, Bool.not_false]
  (try wp_auto)
  iapply fupd_wp
  imod (notif_ropen lp γl np (DFrac.own sync.rfrac.half) ⊤ (fun _ _ => CoPset.mem_full))
    $$ [$Hnp $Hns $Htok] with ⟨Hnp, Hn, Hnp2, Hntk⟩
  imodintro
  wp_apply (hFind lp lm np γl (DFrac.own sync.rfrac) (DFrac.own sync.rfrac.half) sync.rfrac M ri _)
    $$ [$Hpkg $Hlm $HM $Hnp $Hn $Hri $Hls $Hmeta $Htt]
    as %sl ⟨Hlm, HM, Hnp, Hn, Hmeta, Htt, %ps, Hsl, Hslc, %Hps⟩
  · ipureintro; exact Htb
  iapply fupd_wp
  imod (notif_rclose lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hn $Hnp2 $Hntk] with ⟨Hns, Htok⟩
  imodintro
  icases lease.leaseMeta_ids M _ $$ Hmeta with ⟨Hmeta, #Hids⟩
  ihave Hpay := expired_slice γl GA L' M ps HL Hps.2 $$ [$Hguard $Hgr $Hls $Hids]
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Hga Hgc Hg Hnp Hns Hh Hhq Hcp Hmeta Hbl Hdt
      Hdc Hhist] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I', rd0, L'
    iframe Hlm HM Him HI Hrdf Hg
    isplitl [Hga Hgc]
    · iunfold lessorAuth; iexists γga, γcl, γr0; iframe; iframe #
    isplitr
    · ipureintro; exact HL
    iframe Hsz Hls
    isplitl [Hdc Hnp Hns Hh Hhq Hcp Hmeta Hbl Hdt]
    · iunfold lessorExtra; iexists _, np, h, hx, bl; iframe; iframe #
    iexact Hhist
  ihave %Hlen := ownSlice_len sl _ _ $$ Hsl
  by_cases hps : ps = []
  · subst hps
    have h0 : sl.len = W64 0 := by simp at Hlen; word
    rw [h0]
    (try wp_auto)
    iapply HΦ
    iframe Htok Htt
    iunfold lessorRd; iexact Hrd
  have h0 : sl.len ≠ W64 0 := by
    intro h; apply hps; apply List.eq_nil_of_length_eq_zero; rw [h] at Hlen; simp at Hlen; word
  rw [decide_eq_false h0]
  wp_auto_lc 3
  iapply fupd_wp
  imod (lc_fupd_elim_later (E := ⊤)) $$ Hlc1 Hpay with Hpay
  imod (ownSlice_persist sl _ ps) $$ Hsl with #Hsl
  imodintro
  ihave HP : iprop(⌜¬ leasesNoExpiry⌝ ∗ expiredLeases GA sl) $$ [Hpay]
  · isplitr
    · ipureintro; exact Hps.1 hps
    iunfold expiredLeases
    iexists ps
    iframe Hsl Hpay
    ipureintro; exact hps
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `stopC` closed: the lessor stops
      simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γcs
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hchs
      iapply blocking_rcv_implies_nonblocking
      iapply once_recvAu γcs γts _ $$ Hcis
      iintro %v
      (try wp_auto)
      iapply HΦ
      iframe Htok Htt
      iunfold lessorRd; iexact Hrd
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the send: the slice and its payload to `expiredC`'s bag
      simp only [chan.nonblockingClausePre]
      iexists GoSlice, inferInstance, inferInstance, inferInstance, inferInstance, ec, γec, sl
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply is_bag_is_chan $$ Hbag
      unfold nonblockingSendAu
      isplit
      · iapply bag_nb_send_au $$ Hlc2 Hbag HP
        inext
        (try wp_auto)
        iapply HΦ
        iframe Htok Htt
        iunfold lessorRd; iexact Hrd
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · (try wp_auto)
    iapply HΦ
    iframe Htok Htt
    iunfold lessorRd; iexact Hrd

end proof

end EtcdGrove
end Perennial
