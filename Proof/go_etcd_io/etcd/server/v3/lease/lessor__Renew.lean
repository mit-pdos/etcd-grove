/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Renew.lean` (prove-ps2-renew, 2026-11-21; a
names-only trust-boundary contract since the lease-renew plan's C1, 2026-11-01). Under the read lock
(a slot of the lessor's reader pool): `isPrimary`, `demotec` (a close-once channel, `demote_recv`,
through the lock's share of its ghost variable), the lease's lookup and its `revokec` (`leaseMeta`),
`le.cp` (`nil`: `clearRemainingTTL` is `false`); after it, `l.expired()` (stepped into: `Remaining`, with the token
back), and, if expired, the `select` on `revokec`, `demotec` and `stopC` (`lessorStopRecv`), each a
close-once channel whose receive completes only once it is closed (`once_recvAu`); under the write
lock (the guard), the lookup again, `refresh(0)` and `RegisterOrUpdate` of a fresh item; then
`leaseRenewed.Inc()` (`leaseInit`'s counter) and `l.ttl`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Renew
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__isPrimary
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__Remaining
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__refresh
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__RegisterOrUpdate
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell

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

theorem lease.lessor.Renew.wp_proof
    (hPrim : lease.lessor.isPrimary.spec (GF := GF) (hG := hG))
    (hRem : lease.Lease.Remaining.spec (GF := GF) (hG := hG))
    (hRefresh : lease.Lease.refresh.spec (GF := GF) (hG := hG))
    (hReg : lease.LeaseExpiredNotifier.RegisterOrUpdate.spec (GF := GF) (hG := hG)) :
    lease.lessor.Renew.spec (GF := GF) (hG := hG) := by
  intro lp γl id
  wp_start as ⟨#Hinv, #Hpool, Htt, %Hb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hli : (leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, -, -, -, -, ⟨-, ⟨%crn, #Hcrn, #Hcrns⟩⟩, -, -, -, -, #Hnp⟩
  iunfold leaseErrVar at Hnf Hnp
  icases Hnf with ⟨%enf, #Henf, -⟩
  icases Hnp with ⟨%enp, #Henp, -⟩
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, #Hmu, #Hrdi⟩
  -- a reader slot borrowed from the pool with the token, for the read lock
  iapply fupd_wp
  imod lease.lessorRdPool_borrow γl ⊤ (fun _ _ => CoPset.mem_full) $$ [Hpool Htt]
    with ⟨Hrdo, Hback⟩
  · iframe #; iframe
  imodintro
  (try wp_auto)
  iunfold lessorRdOf at Hrdo
  icases Hrdo with ⟨%lp', #Hpin', Hrd⟩
  ihave %Heq := lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
  subst Heq
  iunfold lessorRd at Hrd
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I', %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
    Hhist⟩
  iunfold lessorExtra at Hx
  icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr⟩
  (try wp_auto)
  wp_apply (hPrim lp dc _) $$ [$Hpkg $Hdc] as Hdc
  by_cases hdc : dc = chan.nil
  · -- not the primary
    subst hdc
    simp only [decide_true, Bool.not_true, Bool.not_false]
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp Hmeta
        Hbl Hdt Hhist] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe Hlm HM Him HI Hrdf Ha Hg Hhist
      isplitr
      · ipureintro; exact HL
      iframe Hsz Hls
      iunfold lessorExtra; iexists chan.nil, np, h, hx, bl; iframe; iframe Hstr
    iapply fupd_wp
    imod Hback $$ [Hrd] with Htt
    · iunfold lessorRdOf; iexists lp; iframe Hpin; iunfold lessorRd; iexact Hrd
    imodintro
    (try wp_auto)
    iapply HΦ
    iframe Htt
    iright; ileft
    iexists enp; iframe Henp; (try (ipureintro; rfl))
  simp only [hdc, decide_false, Bool.not_false, Bool.not_true]
  -- `demotec`: a close-once channel, out of the lessor's `demotec` invariant
  iunfold demoteTie at Hdt
  icases Hdt with ⟨%γr', #Hpr', Hgv, #Hout⟩
  wp_auto_lc 1
  iapply fupd_wp
  imod demote_recv γr'.2.2.2.2.2.2.1 _ dc hdc $$ [$Hlc1 $Hgv $Hout] with ⟨Hgv, %γtd, #Hdr⟩
  imodintro
  ihave Hdt : demoteTie γl _ dc $$ [Hgv]
  · iunfold demoteTie; iexists γr'; iframe Hpr' Hout Hgv
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  cases hM : M.lookup id with
  | none =>
    simp only [Option.getD_none]
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp Hmeta
        Hbl Hdt Hhist] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe Hlm HM Him HI Hrdf Ha Hg Hhist
      isplitr
      · ipureintro; exact HL
      iframe Hsz Hls
      iunfold lessorExtra; iexists dc, np, h, hx, bl; iframe; iframe Hstr
    iapply fupd_wp
    imod Hback $$ [Hrd] with Htt
    · iunfold lessorRdOf; iexists lp; iframe Hpin; iunfold lessorRd; iexact Hrd
    imodintro
    (try wp_auto)
    iapply HΦ
    iframe Htt
    iright; iright
    iexists enf; iframe Henf; (try (ipureintro; rfl))
  | some l =>
    simp only [Option.getD_some]
    ihave #Hlo := BigSepM.bigSepM_lookup hM $$ Hls
    ihave #Hlo' := Hlo
    iunfold isLeaseObj at Hlo'
    icases Hlo' with ⟨%Hnn, -⟩
    -- the lease's `revokec`, from its `leaseMeta` (persistent)
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x _) hM).1 $$ Hmeta
      with ⟨Hml, Hmeta⟩
    iunfold leaseMeta at Hml
    icases Hml with ⟨#HID, #Httl, #Hrc, Hrem, Hexp, #HexG⟩
    ihave Hmeta := Hmeta $$ [Hrem Hexp]
    · iunfold leaseMeta; iframe HID Httl Hrc Hrem Hexp HexG
    icases Hrc with ⟨%rc, #Hrc, #Hrr⟩
    simp only [Hnn, decide_false]
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp Hmeta
        Hbl Hdt Hhist] as Hrd
    · inext
      iunfold lessorMu
      iexists lm, im, M, I', rd0, L'
      iframe Hlm HM Him HI Hrdf Ha Hg Hhist
      isplitr
      · ipureintro; exact HL
      iframe Hsz Hls
      iunfold lessorExtra; iexists dc, np, h, hx, bl; iframe; iframe Hstr
    iapply fupd_wp
    imod Hback $$ [Hrd] with Htt
    · iunfold lessorRdOf; iexists lp; iframe Hpin; iunfold lessorRd; iexact Hrd
    imodintro
    (try wp_auto)
    -- `l.expired()`: `l.Remaining() <= 0`, stepped into (its `Remaining` with the token back)
    wp_method_call
    wp_call
    (try wp_auto)
    wp_apply (hRem γl l) $$ [$Hpkg $Hlo $Htt] as %d Htt
    · ipureintro; exact Hb
    (try wp_auto)
    wp_if_destruct
    · -- expired: wait for the revocation, the demotion or the stop
      iunfold lessorStopRecv at Hstr
      icases Hstr with ⟨%sc, %γts, #Hsc, #Hsr⟩
      iunfold revokeRecv at Hrr
      icases Hrr with ⟨%γtr, #Hrr⟩
      iunfold onceRecv at Hrr Hdr Hsr
      icases Hrr with ⟨%γcr, #Hchr, #Hcir⟩
      icases Hdr with ⟨%γcd, #Hchd, #Hcid⟩
      icases Hsr with ⟨%γcs, #Hchs, #Hcis⟩
      (try wp_auto)
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `revokec` closed: the lease was revoked
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rc, γcr
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hchr
        iapply once_recvAu γcr γtr _ $$ Hcir
        iintro %v
        (try wp_auto)
        iapply HΦ
        iframe Htt
        iright; iright
        iexists enf; iframe Henf; (try (ipureintro; rfl))
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `demotec` closed: demoted
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dc, γcd
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hchd
        iapply once_recvAu γcd γtd _ $$ Hcid
        iintro %v
        (try wp_auto)
        iapply HΦ
        iframe Htt
        iright; ileft
        iexists enp; iframe Henp; (try (ipureintro; rfl))
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- `stopC` closed: stopped
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γcs
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hchs
        iapply once_recvAu γcs γts _ $$ Hcis
        iintro %v
        (try wp_auto)
        iapply HΦ
        iframe Htt
        iright; ileft
        iexists enp; iframe Henp; (try (ipureintro; rfl))
      iapply BigAndL.bigAndL_nil.2
      itrivial
    -- not expired (or after the wait): the write lock, through the guard
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hlk, HR⟩
    iunfold lessorMu at HR
    icases HR with ⟨%lm, %im, %M, %I, %rd0, %L, Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hsz, #Hls, Hx,
      Hhist⟩
    iunfold lessorExtra at Hx
    icases Hx with ⟨%dc, %np, %h, %hx, %bl, Hdc, Hnp, Hnot, Hh, Hhq, Hcp, Hmeta, Hbl, Hdt, #Hstr'⟩
    imod (notif_wopen lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot] with ⟨Hnp, Hnot, Hntk⟩
    (try wp_auto)
    wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
    cases hM' : M.lookup id with
    | none =>
      simp only [Option.getD_none]
      (try wp_auto)
      imod (notif_wclose lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
          Hmeta Hbl Hdt Hhist]
      · iframe #
        inext
        iunfold lessorMu
        iexists lm, im, M, I, rd0, L
        iframe Hlm HM Him HI Hrdf Ha Hg Hhist
        isplitr
        · ipureintro; exact HL
        iframe Hsz Hls
        iunfold lessorExtra; iexists dc, np, h, hx, bl; iframe; iframe Hstr'
      (try wp_auto)
      iapply HΦ
      iframe Htt
      iright; iright
      iexists enf; iframe Henf; (try (ipureintro; rfl))
    | some l' =>
      simp only [Option.getD_some]
      ihave #Hlo2 := BigSepM.bigSepM_lookup hM' $$ Hls
      ihave #Hlo2' := Hlo2
      iunfold isLeaseObj at Hlo2'
      icases Hlo2' with ⟨%Hnn2, -⟩
      simp only [Hnn2, decide_false]
      icases (BigSepM.bigSepM_lookup_acc (Φ := fun i x => leaseMeta (GF := GF) i x 1) hM').1 $$ Hmeta
        with ⟨Hml, Hmeta⟩
      iunfold leaseMeta at Hml
      icases Hml with ⟨#HID, ⟨%t, #Httl⟩, #Hrc, ⟨%r, Hrem⟩, ⟨%e, Hexp⟩, #HexG⟩
      (try wp_auto)
      wp_apply (hRefresh l' (W64 0) r t (DFrac.own 1) DFrac.discard e) $$
        [$Hpkg $Hrem $Httl $Hexp $HexG] as ⟨Hrem, -, %e', Hexp⟩
      (try wp_auto)
      iStructNamed «$r0»
      ipersist id
      iunfold notifierAt at Hnot
      icases Hnot with ⟨%Mn, Hnot⟩
      wp_apply (hReg np «$r0_ptr» _ (W64 0) Mn) $$ [$Hpkg $Hnot id time index] as Hnot
      · ileft; iunfold lwtAt; iframe; iframe #
      (try wp_auto)
      ihave Hmeta := Hmeta $$ [Hrem Hexp]
      · iunfold leaseMeta
        iframe HID HexG Hrc
        isplitr
        · iexists t; iexact Httl
        isplitl [Hrem]
        · iexists r; iexact Hrem
        iexists e'; iexact Hexp
      imod (notif_wclose lp γl np ⊤ (fun _ _ => CoPset.mem_full)) $$ [$Hnp $Hnot $Hntk] with ⟨Hnp, Hnot⟩
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hdc Hnp Hnot Hh Hhq Hcp
          Hmeta Hbl Hdt Hhist]
      · iframe #
        inext
        iunfold lessorMu
        iexists lm, im, M, I, rd0, L
        iframe Hlm HM Him HI Hrdf Ha Hg Hhist
        isplitr
        · ipureintro; exact HL
        iframe Hsz Hls
        iunfold lessorExtra; iexists dc, np, h, hx, bl; iframe; iframe Hstr'
      (try wp_auto)
      iunfold counterSpec at Hcrns
      icases Hcrns with #Hcrns
      wp_apply Hcrns
      (try wp_auto)
      iapply HΦ
      iframe Htt
      ileft
      ipureintro; rfl

end proof

end EtcdGrove
end Perennial
