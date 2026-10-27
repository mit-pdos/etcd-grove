/-
Proof of `Spec/EtcdServer__applyEntryNormal.lean`. Lean-first (no Rocq counterpart).

`wp_proofOn` (the auth plan's E3o) proves `specOn`, the step with auth on: the mode-off proof's
structure, with the mode-`on` model (`kvEntryOn`, `kvAppliedOn`) and three applications of an entry
with data: a KV request through the latest-state triple (`apply.Apply.kvSpecL`, the verdict at the
auth row's history, lent out of the row by `auth.ownFuT_lend`), a cluster request through
`apply.Apply.spec` (the log kept), an admin request through the auth row's admin steps
(`adminEntryOn.spec`, the row's history one admin step later). A replayed entry (`v3` false) leaves
the model's state (`kvEntryOn_below`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Lemmas
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ElectionTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.UberOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem ciEff_stLoaded (γ : ApplyNames) (st : ApplyState) :
    ciEff γ (stLoaded γ st).k = ciEff γ st.k := by
  unfold stLoaded; split <;> simp_all [ciEff]

theorem stLoaded_fields (γ : ApplyNames) (st : ApplyState) :
    (stLoaded γ st).p = st.p ∧ (stLoaded γ st).eff = st.eff ∧
      (stLoaded γ st).pending = st.pending := by
  unfold stLoaded; split <;> exact ⟨rfl, rfl, rfl⟩

set_option hygiene false in
/-- The deferred update after an entry processed with no writes (state `{st with p := i}`):
`ci` is below `i`, so it is advanced to `i`; then the postcondition. -/
local macro "tail_skip" : tactic => `(tactic| (
  wp_apply_core (wp_ci_get hC γ ci b { st with p := m.index } Hp) $$ [Hst Hbe] [-]
  · iframe Pci Hci Hinv Hst Hbe
  iintro ⟨Hst, Hbe⟩
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  (try wp_auto)
  rw [decide_eq_true hce]
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  wp_apply hGT e m
  · iexact He
  (try wp_auto)
  obtain ⟨hlp, hle, hlpend⟩ := stLoaded_fields γ { st with p := m.index }
  wp_apply_core (wp_ci_advance hS γ ci (stLoaded γ { st with p := m.index }) m.index m.term
      (by rw [hlpend]; exact Hp) (by rw [hlp]; exact Int.le_refl _)
      (by rw [ciEff_stLoaded]; exact hce)) $$ [Hst] [-]
  · iframe Pci Hci Hinv Hst
  iintro Hst
  (try wp_auto)
  iapply HΦ
  iframe Hbe Hlr Hgr HFS HKV
  (try simp only [↓reduceIte])
  iframe Happ
  iexists st.eff
  have hfin : { stLoaded γ { st with p := m.index } with k := m.index } =
      ({ k := m.index, p := m.index, eff := st.eff, pending := false } : ApplyState) := by
    unfold stLoaded; split <;> simp [Hp]
  rw [hfin] at *
  iexact Hst))

set_option hygiene false in
/-- The deferred update after an entry whose writes went through the hook (state
`⟨i, i, i, false⟩`): `ci` is `i`, nothing to do; then the postcondition. -/
local macro "tail_done" : tactic => `(tactic| (
  wp_apply_core (wp_ci_get hC γ ci b ⟨m.index, m.index, m.index, false⟩ rfl) $$ [Hst Hbe] [-]
  · iframe Pci Hci Hinv Hst Hbe
  iintro ⟨Hst, Hbe⟩
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  (try wp_auto)
  rw [decide_eq_false (by unfold ciEff; rw [ite_eq_right hi0]; exact Int.lt_irrefl _)]
  (try wp_auto)
  iapply HΦ
  iframe Hbe Hlr Hgr HFS HKV
  (try simp only [↓reduceIte])
  iframe Happ
  iexists m.index
  have hfin : stLoaded γ ⟨m.index, m.index, m.index, false⟩ =
      ({ k := m.index, p := m.index, eff := m.index, pending := false } : ApplyState) := by
    unfold stLoaded; rw [ite_eq_right hi0]
  rw [hfin] at *
  iexact Hst))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise's second case (`waitTrig`), as `trig`. -/
local macro "trig'" : tactic => `(tactic| (
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitR at HR
  icases HR with ⟨%d', %rq', %γf', %F', #Hcl', #Hfl', %Hp'⟩
  obtain ⟨hd', hΨ, hpx⟩ := Hp'
  subst hΨ
  ihave %Hdd := idClaim_agree' ρ.ids id d' m.data γf' γf $$ Hcl' Hcl0
  obtain ⟨Hdd, Hγ⟩ := Hdd
  subst Hdd Hγ
  -- (D21e (A)) a registered id is of the member's prefix: the floor its claim recorded
  ihave #HfF := HfFo $$ %hpx
  ihave %HFF := floorAt_agree γf' F' F $$ Hfl' HfF
  subst HFF
  rw [hdec] at hd'
  cases hd'
  iunfold resultΨ
  iexists ar, x.log
  isplitr
  · ipureintro; rfl
  isplitl [HTr]
  · iexact HTr
  isplitl
  rotate_left
  · iexact HeW
  iunfold resultIsW
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert HMint Hcx'
  isplitr
  · ipureintro; exact ⟨Hstep0.1, Hstep0.2, rfl, Hwvf hpx⟩
  iunfold appliedWit
  iexists m.index
  rw [Hrd]
  iframe Hcm HLpre Hmono))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise: every expectation registered under the entry's id is the
proposer's `resultΨ` of the entry's request (the claims agree), which the result meets. -/
local macro "trig" : tactic => `(tactic| (
  iright; iright
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitR at HR
  icases HR with ⟨%d', %rq', %γf', %F', #Hcl', #Hfl', %Hp'⟩
  obtain ⟨hd', hΨ, hpx⟩ := Hp'
  subst hΨ
  ihave %Hdd := idClaim_agree' ρ.ids id d' m.data γf' γf $$ Hcl' Hcl0
  obtain ⟨Hdd, Hγ⟩ := Hdd
  subst Hdd Hγ
  -- (D21e (A)) a registered id is of the member's prefix: the floor its claim recorded
  ihave #HfF := HfFo $$ %hpx
  ihave %HFF := floorAt_agree γf' F' F $$ Hfl' HfF
  subst HFF
  rw [hdec] at hd'
  cases hd'
  iunfold resultΨ
  iexists ar, x.log
  isplitr
  · ipureintro; rfl
  isplitl [HTr]
  · iexact HTr
  isplitl
  rotate_left
  · iexact HeW
  iunfold resultIsW
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert HMint Hcx'
  isplitr
  · ipureintro; exact ⟨Hstep0.1, Hstep0.2, rfl, Hwvf hpx⟩
  iunfold appliedWit
  iexists m.index
  rw [Hrd]
  iframe Hcm HLpre Hmono))

set_option hygiene false in
/-- The deferred update in either state. -/
local macro "tail_any" : tactic => `(tactic| (
  rcases hst1 with rfl | rfl
  · tail_done
  · tail_skip))

set_option maxHeartbeats 800000 in
theorem EtcdServer.applyEntryNormal.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA : apply.Apply.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  intro s γ ci TM E ρ b e m st v3 x γr ot v A
  wp_start as ⟨#Hsrv, #Hewo, #Hreg, #He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, HFS, Hao, #HLv, #Hcm, Hka,
    HRS, #HAm, %HkA, %Hvi, %Hpo, Hv3⟩
  obtain ⟨Hp, Hok, Htyp⟩ := Hpo
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv0 := Hsrv
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomics at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  ihave #Hmono := appliedMono_of_inv s E γr $$ Hainv
  -- the KV model (unit T1): the entry plain, the log after it the model's, certified
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvs at Hkvi'
  icases Hkvi' with ⟨-, -, -, %Hcok⟩
  icases srvApplyKV_idxCert s E ρ.wait x $$ HKV with ⟨HKV, #Hcx⟩
  ihave %Hlx := idxCert_len E.γ.idx x.log $$ Hcx
  icases kvApplied_log γr.raft γr.kv A x $$ Hka with ⟨Hka, %Hxl⟩
  imod kv_applied_step E γr A m x (kvEntry_len _ _ _ x m Hok Hlx) $$ Hkvi Hka HAm with ⟨%Hpe, Hka⟩
  obtain ⟨Hpe, Hxch, Hoff⟩ := Hpe
  -- the start's chain (D19k: no NOSPACE outcome there)
  ihave #Hkvi'' := Hkvi
  iunfold srvKVInvs at Hkvi''
  icases Hkvi'' with ⟨#HkI, -, #HrI, -⟩
  imod kv_log_plain γr.raft γr.kv (A ++ [m]) $$ HkI HrI HAm with %Hpc0
  have Hch0 := Hpc0.2
  -- (D22, 2026-10-23) a covered request: its rest buckets' effect is `dispatch`'s
  have Hpl : ∀ rq, m.data ≠ [] → apply.irrDecode m.data = some rq → plainCover rq :=
    fun rq hd hdec => (Hpc0.1 m (by simp) Htyp hd rq hdec).1
  ihave ⟨Hka, #Hkc⟩ := kvAppliedL_cert _ _ _ _ $$ Hka
  have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + A.length + 1 := by omega
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hrc, #Hq,
    #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Palm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  ihave #Pci : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Perrs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  iunfold lessorOk at Hlok
  icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
  cases v3
  · -- replayed: no backend writes, state unchanged
    wp_auto
    wp_if_destruct
    · -- no data
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      have hl0 : x.log = kvEntry γr.kv.c0 x.chain (kvLeases γr.kv A) x.log m :=
        (kvEntry_nonwrite _ _ _ _ m (Or.inl hnil)).symm
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x m.index hiA hl0 Hxch $$ Hka
      imod applied_predeposit s E γr v m.index x.log x.log Hvi (List.prefix_refl _) $$ Hainv Hao HLv HkL
        with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m false x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
          srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗
          srvRest E γr (A ++ [m])) $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV Hpre Hka
        rw [srvRest_nodata E γr A m Htyp hnil]
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr HFS HKV
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        wp_apply HP
        (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr HFS HKV
    · -- data: the applier, with nothing to write (`ApplyV2storeOnly`)
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKV at HKV
      icases HKV with ⟨%ua, Hua, #Happl, HKV, Hbo, HRA, HAR, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      ihave ⟨HKV, %HaOn⟩ := applyKV_authOn E ua x $$ HKV
      ihave #Hcp := kv_certPre E γr.kv Hcok γr.kv.c0 (kvLeases γr.kv A) x m rq false
        (Hpe Htyp hdata rq hdec).1 Hoff Htyp
        hdata hdec HkA.2 $$ Hkc
      ihave HFSE : E.FS $$ [HFS]
      · rw [HEo.1]; iexact HFS
      ihave HSpF : iprop(if false = true then apply.ciSplit E iprop(True) else iprop(True)) $$ []
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iapply wp_fupd
      iunfold srvRest at HRS
      (try wp_auto)
      wp_apply hA fv.lg e m ua fv.w false E iprop(True) iprop(True) iprop(True) x rq id0 RD
        (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot x.log
        _ $$ [HKV Hwt HRD HFSE HSpF HRS]
        as %ar %id ⟨HRD, HFS, -, #Har, -, %Hid, %x', %out, HKV, HRS, %Hstep0, -, -, #Hdel⟩
      · iframe Happl Hwok' HRD He HKV Hwt Hcp HFSE HSpF HRS
        isplitr
        · iunfold entryRegd at Hreg
          ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
          iexact Hr1
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · ipureintro; exact Hlgnn
        isplitr
        · itrivial
        iframe Hcx
        ipureintro; exact ⟨hdec, hid, hrq, HaOn ▸ hdk⟩
      ihave HFS : srvFS s $$ [HFS]
      · rw [← HEo.1]; iexact HFS
      have Hstep := Hstep0.1
      rw [srvRest_apply E γr A m rq false x x' out Htyp hdata hdec HkA.2 (Hpl rq hdata hdec) Hstep]
      ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E ua x' $$ HKV
      ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
      imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
      (try wp_auto)
      have hes : entryStep m false x x' out := by
        unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
      obtain ⟨hc', hl'⟩ := batchStep_plain γr.kv.c0 (kvLeases γr.kv A) m x x' Hpe Hoff
        (batchStep_of_entryStep γr.kv.c0 m false x x' out Htyp HkA.2 hes)
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x' m.index hiA hl' (hc'.trans Hxch) $$ Hka
      imod applied_predeposit s E γr v m.index x.log x'.log Hvi
        (applyStep_prefix rq false x x' out Hstep) $$ Hainv Hao HLv HkL with Hpre
      imodintro
      wp_pures
      iapply HΦ
      iframe Hbe Hst Hlr Hgr HFS
      iexists x', out
      iframe Hpre Hka HRS
      isplitl
      · iunfold srvApplyKV; iexists ua; isplitl [Hua]; · iexact Hua
        isplitr; · iexact Happl
        isplitl [HKV]; · iexact HKV
        isplitl [Hbo]; · iexact Hbo
        isplitl [HRA]; · iexact HRA
        isplitl [HAR]; · iexact HAR
        iexists fv.w, RD; iframe Hw Hwok' HRD
      isplitr
      · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
      iunfold entryDelivered
      icases Hdel with (%Hwv | #Hg)
      · ileft; ipureintro; right; exact Hwv
      · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩
  · -- the entry `i = p + 1`, above `ci`
    simp only [↓reduceIte]
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce, hld⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      have hl0 : x.log = kvEntry γr.kv.c0 x.chain (kvLeases γr.kv A) x.log m :=
        (kvEntry_nonwrite _ _ _ _ m (Or.inl hnil)).symm
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x m.index hiA hl0 Hxch $$ Hka
      imod applied_predeposit s E γr v m.index x.log x.log Hvi (List.prefix_refl _) $$ Hainv Hao HLv HkL
        with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m true x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
          srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗
          srvRest E γr (A ++ [m])) $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV Hpre Hka
        rw [srvRest_nodata E γr A m Htyp hnil]
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      cases ldr
      · (try wp_auto)
        tail_skip
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        wp_apply HP
        (try wp_auto)
        tail_skip
    · -- data: the applier, in one critical section after the hook, or without writes
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      have hpre : st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
          uint.Z (ciEff γ st.k) < uint.Z m.index := ⟨Hp, hi, hlt, hce⟩
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKV at HKV
      icases HKV with ⟨%ua, Hua, #Happl, HKV, Hbo, HRA, HAR, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      ihave ⟨HKV, %HaOn⟩ := applyKV_authOn E ua x $$ HKV
      ihave #Hcp := kv_certPre E γr.kv Hcok γr.kv.c0 (kvLeases γr.kv A) x m rq true
        (Hpe Htyp hdata rq hdec).1 Hoff Htyp
        hdata hdec HkA.2 $$ Hkc
      obtain ⟨HEP, HEf⟩ := HE
      -- the floor its proposer recorded with the entry's claim (the vertical slice's unit V2)
      -- (and, unit T1, the committed log it is in)
      have he : entryWaitOk ρ E m = iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              (∃ γf : GName, idClaim ρ.ids id m.data γf) ∗ idRegd ρ.ids id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L⌝) := by
        unfold entryWaitOk; rw [ite_eq_left Htyp]
      ihave #Hewo' : iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              (∃ γf : GName, idClaim ρ.ids id m.data γf) ∗ idRegd ρ.ids id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L⌝) $$ []
      · rw [← he]; iexact Hewo
      icases Hewo' with ⟨#Hewc, %Lw, #HLw, %HmLw⟩
      ihave ⟨⟨%γf, #Hcl0⟩, -⟩ := Hewc $$ %rq %id0 %(⟨hdata, hdec, hid⟩)
      ihave #Hgen' := Hgen
      iunfold srvGenAt at Hgen'
      icases Hgen' with ⟨%gidg, -, #Hidg⟩
      -- (D21e (A), stage M4) an id of the member's prefix: the floor its claimer recorded (the
      -- generator's facts); another member's: no waiter here (`reqWaitR`), the empty floor
      ihave Hfl : iprop(|={⊤}=> ∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
          (⌜idPfx id0 = ρ.ids.pfx⌝ -∗ floorAt γf F)) $$ []
      · by_cases hpx : idPfx id0 = ρ.ids.pfx
        · imod idClaim_fact ρ.ids gidg (srvFloorFact E) id0 m.data γf ⊤ (by simp)
            $$ Hidg Hcl0 %hpx with Hff
          icases Hff with >#Hff
          iunfold srvFloorFact at Hff
          icases Hff with ⟨%F, #HfF, #HcF⟩
          imodintro
          iexists F
          iframe HcF
          iintro -
          iexact HfF
        · imod mvcc.idxCert_nil E.γ.idx with #HcF
          imodintro
          iexists []
          iframe HcF
          iintro %hpx'
          exact absurd hpx' hpx
      imod Hfl with ⟨%F, #HcF, #HfFo⟩
      -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
      ihave HFSE : E.FS $$ [HFS]
      · rw [HEo.1]; iexact HFS
      ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
            uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
      · iunfold apply.ciSplit
        iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
        iexists iprop(applyThread γ st ∗ applyBackend γ ci b)
        iframe Hst' Hbe'
        isplitr
        · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld⟩
        iintro ⟨Hst', Hbe'⟩
        iframe Hst' Happ' Hbe'
        ipureintro; exact Hf'
      ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
            m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
      · simp only [↓reduceIte]; iexact HSp
      (try wp_auto)
      wp_apply hA fv.lg e m ua fv.w true E
        iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
        iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b)
        iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b) x rq id0 RD
        (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
        _ $$ [Hst Happ Hbe HKV Hwt HRD HFSE HSpT HRS] as %ar %id
          ⟨HRD, HFS, Hout, #Har, HTr, %Hid, %x', %out, HKV, HRS, %Hstep0, HRes, -, #Hdel⟩
      · iunfold srvRest at HRS
        iframe Happl Hwok' HRD He HKV Hwt Hcp HFSE HSpT HRS
        isplitr
        · iunfold entryRegd at Hreg
          ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
          iexact Hr1
        simp only [↓reduceIte]
        rw [HEP, HEf]
        isplitr
        · ipureintro; exact Hlgnn
        isplitr
        · isplitr
          · iunfold hookSpec at Hhook
            ihave #Hh := Hhook $$ %st %m.index %m.term %b
            imodintro
            iexact Hh
          · iintro ⟨Hdone, Hst, Happ, Hbe⟩
            imod writes_done γ { st with k := m.index, pending := true } rfl $$ Hinv Hst
              with ⟨Hst, Htok⟩
            iunfold hookDone at Hdone
            icases Hdone with ⟨%mm, Hmt, HTM, #Hreg⟩
            imodintro
            iframe Happ Hbe
            isplitl [Hmt HTM Htok]
            · iunfold batchLockInv; iexists mm; iframe; iexact Hreg
            iexact Hst
        · iframe Hst Happ Hbe HcF
          ipureintro; exact ⟨hpre, hdec, hid, hrq, HaOn ▸ hdk⟩
      ihave HFS : srvFS s $$ [HFS]
      · rw [← HEo.1]; iexact HFS
      have Hstep := Hstep0.1
      rw [srvRest_apply E γr A m rq true x x' out Htyp hdata hdec HkA.2 (Hpl rq hdata hdec) Hstep]
      ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
      · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
        · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
        · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
          imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
      imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
      ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E ua x' $$ HKV
      ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
      imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, HMint⟩
      have hes : entryStep m true x x' out := by
        unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
      obtain ⟨hc', hl'⟩ := batchStep_plain γr.kv.c0 (kvLeases γr.kv A) m x x' Hpe Hoff
        (batchStep_of_entryStep γr.kv.c0 m true x x' out Htyp HkA.2 hes)
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x' m.index hiA hl' (hc'.trans Hxch) $$ Hka
      imod applied_predeposit s E γr v m.index x.log x'.log Hvi
        (applyStep_prefix rq true x x' out Hstep) $$ Hainv Hao HLv HkL with Hpre
      icases srvAppliedPre_log γr v m.index x'.log $$ Hpre with ⟨Hpre, #HLpre⟩
      ihave HKV : iprop(∃ (x'' : apply.ApplyKV) (out' : apply.ApplyOut), srvApplyKV s E ρ.wait x'' ∗
          ⌜entryStep m true x x'' out'⌝ ∗ entryDelivered ρ.wait m ot out' ∗
          srvAppliedPre γr v m.index x''.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x'' ∗
          srvRest E γr (A ++ [m])) $$ [HKV Hua Hbo HRD HRA HAR Hpre Hka HRS]
      · iexists x', out
        iframe Hpre Hka HRS
        isplitl
        · iunfold srvApplyKV; iexists ua; isplitl [Hua]; · iexact Hua
          isplitr; · iexact Happl
          isplitl [HKV]; · iexact HKV
          isplitl [Hbo]; · iexact Hbo
          isplitl [HRA]; · iexact HRA
          isplitl [HAR]; · iexact HAR
          iexists fv.w, RD; iframe Hw Hwok' HRD
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
        iunfold entryDelivered
        icases Hdel with (%Hwv | #Hg)
        · ileft; ipureintro; right; exact Hwv
        · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        tail_any
      iunfold apply.resultErrOk at Har
      icases Har with (%Hnull | ⟨%err, #Herr, #HerrIs⟩)
      · exact absurd Hnull Hif
      have Har0 : ar ≠ null := Hif
      ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Perrs
      icases Hei with ⟨⟨%ens, #Hens, %Hensp⟩, -⟩
      -- D19k: the result's error is not `ErrNoSpace`'s (a plain request at the start's chain),
      -- so `errors.Is(ar.Err, ErrNoSpace)` is `false` and the NOSPACE alarm branch is dead
      ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Papp
      icases Hai with ⟨-, -, #Hev⟩
      ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpace rq x x' ar out (Hpe Htyp hdata rq hdec).1
        (Hxch.trans Hch0) Hstep $$ Hev HRes
      icases Hnn with (%Hn0 | ⟨%err', #Herr', #Hnn⟩)
      · exact absurd Hn0 Har0
      icombine Herr Herr' gives %Heq
      subst Heq
      (try wp_auto)
      wp_apply (wp_Is_notNoSpace hIs err ens Hensp) $$ []
      · iframe #
      iunfold waitInv at Hwok
      icases Hwok with ⟨⟨%RD0, Hwok⟩, #Hwn⟩
      iunfold isWait at Hwok
      icases Hwok with ⟨%wi, %Hwi, -, #HTrig, -⟩
      subst Hid
      -- the entry at its position after the applied raft log `A`, whose model the entry met
      -- (unit W-M3: the proposer's update fired at the state of `x.log`)
      ihave #HeW : iprop(entryWit ρ rq x.log) $$ []
      · iunfold entryWit
        iexists A ++ [m], A.length, m, id, γf
        simp only [ReqNames.raft, ReqNames.kv, Hrd]
        iframe HAm Hcl0
        ipureintro
        refine ⟨by simp, Htyp, hdec, hid, ?_⟩
        rw [List.take_left' rfl, Hxl]
      -- the caller's certificate of the log after (unit W-M3)
      ihave #Hcx' : iprop(mvcc.certOk E.γ x'.log) $$ []
      · rw [hl']; iapply kvCert_certOk γr.kv E.γ Hcok $$ Hkc
      -- not `ErrNoSpace` (D19k: `errors.Is` answered `false`): hand the result to the waiter
      (try wp_auto)
      rw [Hwi]
      (try wp_auto)
      (try dsimp only)
      ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
      -- (linkv-txn stage B1) the result handed over is of a full application: the outcome not
      -- waived, or the registration gone (nothing is sent), or the id another member's
      ihave %Hot : ⌜ot = none → m.data ≠ [] → idPfx id ≠ ρ.ids.pfx⌝ $$ []
      · iunfold entryRegd at Hreg
        ihave ⟨-, %Ho⟩ := Hreg $$ %rq %id %(⟨hdec, hid⟩)
        ipureintro; exact Ho
      icases Hdel with (%Hwv | #Hg)
      · have Hwvf : idPfx id = ρ.ids.pfx → out.waived = false := fun _ => Hwv
        wp_apply HT $$ [HRes HTr HMint]
        · trig
        (try wp_auto)
        tail_any
      · cases ot with
        | some t =>
          wp_apply HT $$ []
          · ileft; iexists t; iunfold waitGoneOpt at Hg; iexact Hg
          (try wp_auto)
          tail_any
        | none =>
          have Hwvf : idPfx id = ρ.ids.pfx → out.waived = false := fun h => absurd h (Hot rfl hdata)
          wp_apply HT $$ [HRes HTr HMint]
          · trig
          (try wp_auto)
          tail_any

variable [apkg_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- The uber-applier's row put back (`srvApplyKVOn`) at the names of the call. -/
local macro "repack" : tactic => `(tactic| (
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Happl
  isplitl [HKV]
  · iexact HKV
  isplitl [Hbo]
  · iexact Hbo
  isplitl [HRA]
  · iexact HRA
  isplitl [HAR]
  · iexact HAR
  iexists fv.w, RD
  iframe Hw Hwok' HRD))

set_option hygiene false in
/-- The hook's triple and the closing of `Q` (the premise `apply.Apply`'s triples take with `v3`). -/
local macro "hook_pre" : tactic => `(tactic| (
  ihave Hhk : iprop(□ ({{ E.P ∗ iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
        applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
          uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) }}
        (App (Val E.f) (Val #())) {{ RET #(); iprop(hookDone γ TM ∗
          applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b) }}) ∗
      (iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b) ={⊤}=∗
        E.P ∗ iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b))) $$ []
  · rw [HEP, HEf]
    isplitr
    · iunfold hookSpec at Hhook
      ihave #Hh := Hhook $$ %st %m.index %m.term %b
      imodintro
      iexact Hh
    · iintro ⟨Hdone, Hst, Happ, Hbe⟩
      imod writes_done γ { st with k := m.index, pending := true } rfl $$ Hinv Hst
        with ⟨Hst, Htok⟩
      iunfold hookDone at Hdone
      icases Hdone with ⟨%mm, Hmt, HTM, #Hreg⟩
      imodintro
      iframe Happ Hbe
      isplitl [Hmt HTM Htok]
      · iunfold batchLockInv; iexists mm; iframe; iexact Hreg
      iexact Hst))

set_option hygiene false in
/-- A replayed entry's application (`v3` false) to the postcondition: the log and the chain kept
(`hkeep`), the auth state too (`HAR` at `sa`), the rest buckets one entry later (`HRS`). -/
local macro "tail_off" : tactic => `(tactic| (
  ihave HFS : srvFS s $$ [HFS]
  · rw [← HEo.1]; iexact HFS
  ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E ua x' $$ HKV
  ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
  imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
  (try wp_auto)
  ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) (sa, x'.log) $$ [Hka]
  · irevert Hka; rw [kvEntryOn_below _ _ _ m hv, hkeep.1]; iintro Hka; iexact Hka
  ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x' sa m.index hiA (hkeep.2.trans Hxch) $$ Hka
  imod applied_predepositM true s E γr v m.index x.log x'.log Hvi
    (applyStep_prefix rq false x x' out Hstep) $$ Hainv Hao HLv HkL with Hpre
  imodintro
  first | iapply HΦ | (wp_pure; wp_pure; iapply HΦ)
  iframe Hbe Hst Hlr Hgr HFS
  iexists x', out, sa
  iframe Hpre Hka HRS
  isplitl
  · repack
  isplitr
  · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
  iunfold entryDelivered
  icases Hdel with (%Hwv | #Hg)
  · ileft; ipureintro; right; exact Hwv
  · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise in the mode `on`: every expectation registered under the entry's
id is the proposer's `resultΨOn` of the entry's request, which the result meets. -/
local macro "trig_on" : tactic => `(tactic| (
  iright; iright
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitRM at HR
  icases HR with ⟨%d', %rq', %γf', %F', #Hcl', #Hfl', %Hp'⟩
  obtain ⟨hd', hΨ, hpx⟩ := Hp'
  subst hΨ
  ihave %Hdd := idClaim_agree' ρ.ids id d' m.data γf' γf $$ Hcl' Hcl0
  obtain ⟨Hdd, Hγ⟩ := Hdd
  subst Hdd Hγ
  ihave #HfF := HfFo $$ %hpx
  ihave %HFF := floorAt_agree γf' F' F $$ Hfl' HfF
  subst HFF
  rw [hdec] at hd'
  cases hd'
  rw [resultΨM_true]
  iunfold resultΨOn
  iexists ar, x.log, sa
  isplitr
  · ipureintro; rfl
  isplitl [HTr]
  · iexact HTr
  isplitl
  rotate_left
  · iexact HeW
  iunfold resultIsWOn
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert HMint Hcx'
  isplitr
  · ipureintro; exact ⟨Hstep0.1, Hstep0.2, rfl, Hwvf hpx, Htie⟩
  iunfold appliedWit
  iexists m.index
  rw [Hrd]
  iframe Hcm HLpre Hmono))

set_option hygiene false in
/-- An entry's application above the start (`v3` true) to the postcondition: the deferred update,
the result handed to the waiter (the NOSPACE branch dead, `Hnn`), at the call's names: the step
and floor (`Hstep0`), the auth layer's verdict tied (`Htie`), the model's state after it
(`hmod`, `hc'`), the auth row at `sa'` (`HAR`), the rest buckets one entry later (`HRS`). -/
local macro "tail_on" sa':term : tactic => `(tactic| (
  ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
      ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
      ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
  · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
    · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
    · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
  imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
  ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E ua x' $$ HKV
  ihave %Hlen := idxCert_len E.γ.idx x'.log $$ Hcert
  imod revAuth_step E x.log x'.log (applyStep_grow Hstep0.1) Hlen ⊤ $$ HRA with ⟨HRA, HMint⟩
  ihave #Hcx' : iprop(mvcc.certOk E.γ x'.log) $$ []
  · have hl2 : x'.log = (kvEntryOn γr.kv.c0 x.chain (sa, x.log) m).2 := by rw [← hmod]
    rw [hl2]; iapply kvCert_certOk γr.kv E.γ Hcok $$ Hkc
  ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) ($sa', x'.log) $$ [Hka]
  · rw [hmod]; iexact Hka
  ihave ⟨Hka, -, %Hafter⟩ := kvAppliedLOn_cert _ _ _ _ _ $$ Hka
  ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x' $sa' m.index hiA (hc'.trans Hxch) $$ Hka
  -- (E3t) the auth state after the entry published, for the waiter
  imod srvAuthApplyResB_publish s ua E γa $sa' hM $$ Hb HAR with ⟨HAR, #HpA⟩
  imod applied_predepositM true s E γr v m.index x.log x'.log Hvi
    (applyStep_prefix rq true x x' out Hstep0.1) $$ Hainv Hao HLv HkL with Hpre
  icases srvAppliedPre_log γr v m.index x'.log $$ Hpre with ⟨Hpre, #HLpre⟩
  ihave HKV : iprop(∃ (x'' : apply.ApplyKV) (out' : apply.ApplyOut) (sa'' : auth.AuthState),
      srvApplyKVOn s E ρ.wait x'' sa'' ∗ ⌜entryStep m true x x'' out'⌝ ∗
      entryDelivered ρ.wait m ot out' ∗ srvAppliedPre γr v m.index x''.log ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x'' sa'' ∗ srvRest E γr (A ++ [m]))
      $$ [HKV Hua Hbo HRD HRA HAR Hpre Hka HRS]
  · iexists x', out, $sa'
    iframe Hpre Hka HRS
    isplitl
    · repack
    isplitr
    · ipureintro; unfold entryStep; rw [ite_eq_right hdata]
      exact ⟨rq, id0, hdec, hid, Hstep0.1⟩
    iunfold entryDelivered
    icases Hdel with (%Hwv | #Hg)
    · ileft; ipureintro; right; exact Hwv
    · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    tail_any
  iunfold apply.resultErrOk at Har
  icases Har with (%Hnull | ⟨%err, #Herr, #HerrIs⟩)
  · exact absurd Hnull Hif
  have Har0 : ar ≠ null := Hif
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Perrs
  icases Hei with ⟨⟨%ens, #Hens, %Hensp⟩, -⟩
  icases Hnn with (%Hn0 | ⟨%err', #Herr', #Hnn⟩)
  · exact absurd Hn0 Har0
  icombine Herr Herr' gives %Heq
  subst Heq
  (try wp_auto)
  wp_apply (wp_Is_notNoSpace hIs err ens Hensp) $$ []
  · iframe #
  iunfold waitInvM at Hwok
  icases Hwok with ⟨⟨%RD0, Hwok⟩, #Hwn⟩
  iunfold isWait at Hwok
  icases Hwok with ⟨%wi, %Hwi, -, #HTrig, -⟩
  subst Hid
  -- the entry at its position after the applied raft log `A`, whose mode-`on` model is the
  -- auth state and the log the entry met
  ihave #HeW : iprop(entryWitOn E.authMode ρ rq x.log sa) $$ []
  · iunfold entryWitOn
    iexists A ++ [m], A.length, m, id, γf
    simp only [ReqNames.raft, ReqNames.kv, Hrd]
    iframe HAm Hcl0
    isplitr
    · ipureintro
      refine ⟨by simp, Htyp, hdec, hid, ?_⟩
      rw [List.take_left' rfl, ← Hxl]
    have htk : (A ++ [m]).take (A.length + 1) = A ++ [m] := List.take_of_length_le (by simp)
    rw [htk, ← Hafter]
    iexact HpA
  (try wp_auto)
  rw [Hwi]
  (try wp_auto)
  (try dsimp only)
  ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
  ihave %Hot : ⌜ot = none → m.data ≠ [] → idPfx id ≠ ρ.ids.pfx⌝ $$ []
  · iunfold entryRegd at Hreg
    ihave ⟨-, %Ho⟩ := Hreg $$ %rq %id %(⟨hdec, hid⟩)
    ipureintro; exact Ho
  icases Hdel with (%Hwv | #Hg)
  · have Hwvf : idPfx id = ρ.ids.pfx → out.waived = false := fun _ => Hwv
    wp_apply HT $$ [HRes HTr HMint]
    · trig_on
    (try wp_auto)
    tail_any
  · cases ot with
    | some t =>
      wp_apply HT $$ []
      · ileft; iexists t; iunfold waitGoneOpt at Hg; iexact Hg
      (try wp_auto)
      tail_any
    | none =>
      have Hwvf : idPfx id = ρ.ids.pfx → out.waived = false := fun h => absurd h (Hot rfl hdata)
      wp_apply HT $$ [HRes HTr HMint]
      · trig_on
      (try wp_auto)
      tail_any))

set_option maxHeartbeats 1600000 in
theorem EtcdServer.applyEntryNormal.wp_proofOn
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA : apply.Apply.spec (GF := GF) (hG := hG))
    (hK : apply.Apply.kvSpecL (GF := GF) (hG := hG))
    (hAd : adminEntryOn.spec (GF := GF) (hG := hG))
    (hRange : apply.authApplierV3.Range.specL (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.specL (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.specL (GF := GF) (hG := hG))
    (hUA : apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (hApplyL : apply.authApplierV3.Apply.specL (GF := GF) (hG := hG))
    (hApply : apply.applierV3backend.Apply.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  intro s γ ci TM E ρ b e m st v3 x γr ot v A γa sa hM
  wp_start as ⟨#Hsrv, #Hlnil, #Hewo, #Hreg, #He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, HFS, Hlc, Hao, #HLv,
    #Hcm, Hka, HRS, #HAm, %HkA, %Hvi, %Hpo, Hv3⟩
  obtain ⟨Hp, Hok, Htyp, Hrb⟩ := Hpo
  have hAuthOn : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  wp_apply wp_with_defer as %defer defer
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomicsM at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  ihave #Hmono := appliedMono_of_invM true s E γr $$ Hainv
  ihave #Hkvi : srvKVInvsOn E γr srvAuthSt0 $$ []
  · rw [← srvKVInvsM_true]; iexact Hkvi
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvsOn at Hkvi'
  icases Hkvi' with ⟨-, -, -, %Hcok⟩
  icases srvApplyKVOn_idxCert s E ρ.wait x sa $$ HKV with ⟨HKV, #Hcx, %HaOn⟩
  ihave %Hlx := idxCert_len E.γ.idx x.log $$ Hcx
  -- the mode-`on` model before the entry: `(sa, x.log)`, the start's chain
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hka, %Hxch0⟩
  icases kvAppliedLOn_cert _ _ _ _ _ $$ Hka with ⟨Hka, -, %Hxl⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa $$ [Hka]
  · iunfold kvAppliedOn; iframe Hka; ipureintro; exact Hxch0
  -- the model's step (E2 of the auth plan): the entry admitted and determinate, its state after
  imod kv_applied_step_on E γr srvAuthSt0 A m x sa (kvEntryOn_len _ _ sa x m Hok Hlx)
    $$ Hkvi Hka HAm with ⟨%Hpe, Hka⟩
  obtain ⟨Hpe, Hdet, Hxch, Hch⟩ := Hpe
  icases kvAppliedLOn_cert _ _ _ _ _ $$ Hka with ⟨Hka, #Hkc, -⟩
  have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + A.length + 1 := by omega
  iunfold srvFieldsAtM at Hfv
  icases Hfv with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl,
    #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Palm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  ihave #Pci : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Perrs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  iunfold lessorOk at Hlok
  icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
  cases v3
  · -- replayed: no backend writes, the model's state unchanged
    have hv : ¬ uint.Z γr.kv.c0 < uint.Z m.index := fun h => by
      have := HkA.2; simp only [decide_eq_true h] at this; cases this
    wp_auto
    wp_if_destruct
    · -- no data
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) (sa, x.log) $$ [Hka]
      · irevert Hka; rw [kvEntryOn_nodata γr.kv.c0 x.chain (sa, x.log) m hnil]; iintro Hka
        iexact Hka
      ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x sa m.index hiA Hxch $$ Hka
      imod applied_predepositM true s E γr v m.index x.log x.log Hvi (List.prefix_refl _)
        $$ Hainv Hao HLv HkL with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
          srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m false x x' out⌝ ∗
          entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m]))
          $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped, sa
        iframe HKV Hpre Hka
        rw [srvRest_nodata E γr A m Htyp hnil]
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr HFS HKV
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        wp_apply HP
        (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr HFS HKV
    · -- data: the applier, with nothing to write
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKVOn at HKV
      icases HKV with ⟨%ua, Hua, #Hb, #Happl, HKV, Hbo, HRA, HAR, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      iunfold srvRest at HRS
      rcases Hpe Htyp hdata rq hdec with ⟨⟨hp, hpk⟩, -, -⟩ | ⟨hadm, hns⟩
      · -- a plain request: `apply.Apply`
        have hrq' : apply.rqOk x.log rq :=
          hrq.resolve_right (fun h => adminKindOk_notPutget rq h hpk)
        ihave #Hcp : apply.certPreV false E x.chain rq x.log $$ []
        · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave HSpF : iprop(if false = true then apply.ciSplit E iprop(True) else iprop(True)) $$ []
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        iapply wp_fupd
        (try wp_auto)
        wp_apply hA fv.lg e m ua fv.w false E iprop(True) iprop(True) iprop(True) x rq id0 RD
          (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot x.log
          _ $$ [HKV Hwt HRD HFSE HSpF HRS]
          as %ar %id ⟨HRD, HFS, -, #Har, -, %Hid, %x', %out, HKV, HRS, %Hstep0, -, -, #Hdel⟩
        · iframe Happl Hwok' HRD He HKV Hwt Hcp HFSE HSpF HRS
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          simp only [Bool.false_eq_true, ↓reduceIte]
          isplitr
          · ipureintro; exact Hlgnn
          isplitr
          · itrivial
          iframe Hcx
          ipureintro; exact ⟨hdec, hid, hrq', HaOn ▸ hdk⟩
        have Hstep := Hstep0.1
        rw [srvRest_apply E γr A m rq false x x' out Htyp hdata hdec HkA.2 hp Hstep]
        have hkeep := applyStep_plain_false rq x x' out hp Hstep
        tail_off
      · -- an admin request: the auth row's admin steps (`adminEntryOn`), nothing applied
        have hna := adminKindOk_needAdmin rq hadm
        icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %hs, #Hasf, #Hlend,
          #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
        ihave #HUA := srv_uberAuthStepsL_at hUA hRA hUGR hRGP hAE hApplyL hApply s ua E γa stl bel T hM
          $$ []
        · isplitr
          · iPkgInit
          iframe Hb Hasf Hsteps
        iapply wp_fupd
        (try wp_auto)
        wp_apply hAd fv.lg e m ua fv.w false E iprop(True) iprop(True) iprop(True) x rq id0 RD
          (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot γa stl
          bel T sa _ hM hna hns $$ [HKV HRD Hfu Htie HT Htp HRS Hlc]
          as %ar %id ⟨HRD, -, #Har, -, %Hid, %x', %out, HKV, %Hstep0, -, #Hdel, -, -, HRS, HT,
            Htp, %hs', %sa', Hfu, Htie, %Hsa'⟩
        · simp only [↓reduceIte, Bool.false_eq_true]
          iframe HUA Hwok' HRD He HKV HT Htp Hwba Hlend HRS Hlc
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          isplitr
          · ipureintro; exact Hlgnn
          isplitr
          · ipureintro; exact ⟨hdec, hid, hadm, HaOn ▸ hdk, Hrb⟩
          isplitr
          · ipureintro; rw [Hch, hAuthOn]; rfl
          iexists hs; iframe Hfu Htie; ipureintro; exact Hhl
        obtain ⟨Hstep, hl', hc'⟩ := Hstep0
        have hkeep : x'.log = x.log ∧ x'.chain = x.chain := ⟨hl', hc'⟩
        have hsa' : sa' = sa := by simpa using Hsa'.2
        ihave HAR := Hcl $$ %hs' %sa Hfu Htie %(by rw [← hsa']; exact Hsa'.1) HT Htp
        ihave HRS : srvRest E γr (A ++ [m]) $$ [HRS]
        · rw [srvRest_admin E γr A m rq Htyp hdata hdec hadm]; iunfold srvRest; iexact HRS
        ihave HFS : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        tail_off
  · -- the entry `i = p + 1`, above `ci`
    simp only [↓reduceIte]
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce, hld⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    have hv : uint.Z γr.kv.c0 < uint.Z m.index := of_decide_eq_true HkA.2.symm
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) (sa, x.log) $$ [Hka]
      · irevert Hka; rw [kvEntryOn_nodata γr.kv.c0 x.chain (sa, x.log) m hnil]; iintro Hka
        iexact Hka
      ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x sa m.index hiA Hxch $$ Hka
      imod applied_predepositM true s E γr v m.index x.log x.log Hvi (List.prefix_refl _)
        $$ Hainv Hao HLv HkL with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
          srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m true x x' out⌝ ∗
          entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m]))
          $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped, sa
        iframe HKV Hpre Hka
        rw [srvRest_nodata E γr A m Htyp hnil]
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      cases ldr
      · (try wp_auto)
        tail_skip
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        wp_apply HP
        (try wp_auto)
        tail_skip
    · -- data: the applier, in one critical section after the hook, or without writes
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      have hpre : st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
          uint.Z (ciEff γ st.k) < uint.Z m.index := ⟨Hp, hi, hlt, hce⟩
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKVOn at HKV
      icases HKV with ⟨%ua, Hua, #Hb, #Happl, HKV, Hbo, HRA, HAR, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      obtain ⟨HEP, HEf⟩ := HE
      -- the floor its proposer recorded with the entry's claim (and the committed log it is in)
      have he : entryWaitOk ρ E m = iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              (∃ γf : GName, idClaim ρ.ids id m.data γf) ∗ idRegd ρ.ids id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L⌝) := by
        unfold entryWaitOk; rw [ite_eq_left Htyp]
      ihave #Hewo' : iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              (∃ γf : GName, idClaim ρ.ids id m.data γf) ∗ idRegd ρ.ids id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L⌝) $$ []
      · rw [← he]; iexact Hewo
      icases Hewo' with ⟨#Hewc, %Lw, #HLw, %HmLw⟩
      ihave ⟨⟨%γf, #Hcl0⟩, -⟩ := Hewc $$ %rq %id0 %(⟨hdata, hdec, hid⟩)
      ihave #Hgen' := Hgen
      iunfold srvGenAt at Hgen'
      icases Hgen' with ⟨%gidg, -, #Hidg⟩
      ihave Hfl : iprop(|={⊤}=> ∃ F : mvcc.Log, mvcc.idxCert E.γ.idx F ∗
          (⌜idPfx id0 = ρ.ids.pfx⌝ -∗ floorAt γf F)) $$ []
      · by_cases hpx : idPfx id0 = ρ.ids.pfx
        · imod idClaim_fact ρ.ids gidg (srvFloorFact E) id0 m.data γf ⊤ (by simp)
            $$ Hidg Hcl0 %hpx with Hff
          icases Hff with >#Hff
          iunfold srvFloorFact at Hff
          icases Hff with ⟨%F, #HfF, #HcF⟩
          imodintro
          iexists F
          iframe HcF
          iintro -
          iexact HfF
        · imod mvcc.idxCert_nil E.γ.idx with #HcF
          imodintro
          iexists []
          iframe HcF
          iintro %hpx'
          exact absurd hpx' hpx
      imod Hfl with ⟨%F, #HcF, #HfFo⟩
      ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Papp
      icases Hai with ⟨-, -, #Hev⟩
      hook_pre
      iunfold srvRest at HRS
      rcases Hpe Htyp hdata rq hdec with ⟨⟨hp, hpk⟩, hz, hsa⟩ | ⟨hadm, hns⟩
      · have hna := plainCover_needAdmin rq hp hpk
        have hrq' : apply.rqOk x.log rq :=
          hrq.resolve_right (fun h => adminKindOk_notPutget rq h hpk)
        -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
              uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
        · iunfold apply.ciSplit
          iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
          iexists iprop(applyThread γ st ∗ applyBackend γ ci b)
          iframe Hst' Hbe'
          isplitr
          · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld⟩
          iintro ⟨Hst', Hbe'⟩
          iframe Hst' Happ' Hbe'
          ipureintro; exact Hf'
        ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
              m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
              uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
        · simp only [↓reduceIte]; iexact HSp
        by_cases hkv : apply.isKVKind (apply.dispatchKind rq) = true
        · -- a KV request: the latest-state triple (`kvSpecL`), the verdict at the row's history
          icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %hs, #Hasf,
            #Hlend, #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
          ihave ⟨%stl', #Hasf', #HUK⟩ := srv_uberKVL_on hRange hDel hPut hTxn s ua E γa hM
            $$ []
          · isplitr
            · iPkgInit
            iframe Hb Hlnil
          icombine Hasf Hasf' gives %Hst
          have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
          subst Hst'
          ihave ⟨HL, HLback⟩ := auth.ownFuT_lend stl γa hs $$ [Hfu Htie]
          · iframe Hfu Htie
          ihave #HcpW : apply.certPreVW true E x.chain rq x.log
              (apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend)
                rq x.log) $$ []
          · rw [hM, Hch]
            iapply kv_certPreVW_on E γr.kv Hcok γr.kv.c0 (sa, x.log) m rq Htyp hdata hdec hv hna hkv
              hp γa hs Hhl hz Hdet
            rw [← Hch]; iexact Hkc
          (try wp_auto)
          wp_apply hK fv.lg e m ua fv.w true E
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ (.quota .backend) (auth.latestRes stl (.on γa)) hs
            $$ [Hst Happ Hbe HKV Hwt HRD HFSE HSpT HRS HL Hhk] as %ar %id
              ⟨HRD, HFS, Hout, #Har, HTr, %Hid, %x', %out, HKV, HRS, %Hstep0, HRes, -, HL, %HXo,
                #Hdel⟩
          · simp only [↓reduceIte]
            iframe HUK Hwok' HRD He HKV Hwt HcpW HFSE HSpT HRS HL Hhk
            isplitr
            · iunfold entryRegd at Hreg
              ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
              iexact Hr1
            isplitr
            · ipureintro; exact Hlgnn
            iframe Hst Happ Hbe HcF
            isplitr
            · ipureintro; exact hpre
            isplitr
            · ipureintro; exact ⟨hdec, hid, hrq', HaOn ▸ hdk⟩
            ipureintro
            refine ⟨by rw [Hch, hAuthOn]; rfl, hkv, ?_⟩
            rw [hM]; exact kvShapedL_of_log _ hs rq hz hsa
          have HXo' : ∀ o b, out = .dispatched o b → apply.kvOutL (.on γa) hs
              (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o := by
            intro o b h; have := HXo o b h rfl; rwa [hM] at this
          obtain ⟨hc', hmod⟩ := kvOn_after_kv γr.kv.c0 sa x x' m rq out Htyp hdata hdec hv hna hkv hp
            γa hs Hhl hz Hdet Hch Hstep0.1 HXo'
          have Htie : authTie sa rq out := authTie_of_kvOutL γa hs sa Hhl rq x.log out hz HXo'
          ihave ⟨Hfu, Htie'⟩ := HLback $$ HL
          ihave HAR := Hcl $$ %hs %sa Hfu Htie' %Hhl HT Htp
          ihave HFS : srvFS s $$ [HFS]
          · rw [← HEo.1]; iexact HFS
          rw [srvRest_apply E γr A m rq true x x' out Htyp hdata hdec HkA.2 hp Hstep0.1]
          ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpaceOn rq x x' ar out hp Hch Hstep0.1
            $$ Hev HRes
          tail_on sa
        · -- a cluster request: `apply.Apply`, the log kept
          have hkv' : apply.isKVKind (apply.dispatchKind rq) = false := by simpa using hkv
          obtain ⟨hw, hfl⟩ := putget_nonKV _ hpk hkv'
          have hkeepM := kvEntryOn_keep γr.kv.c0 x.chain (sa, x.log) m rq Htyp hdata hdec hna hw
          ihave #Hcp : apply.certPreV true E x.chain rq x.log $$ []
          · simp only [apply.certPreV, ↓reduceIte]
            iapply kv_certPre_keep E γr.kv Hcok x.chain rq x.log hp hw
            have hl0 : (kvEntryOn γr.kv.c0 x.chain (sa, x.log) m).2 = x.log := by rw [hkeepM]
            irevert Hkc; rw [hl0]; iintro #Hkc; iexact Hkc
          (try wp_auto)
          wp_apply hA fv.lg e m ua fv.w true E
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ $$ [Hst Happ Hbe HKV Hwt HRD HFSE HSpT HRS Hhk] as %ar %id
              ⟨HRD, HFS, Hout, #Har, HTr, %Hid, %x', %out, HKV, HRS, %Hstep0, HRes, -, #Hdel⟩
          · simp only [↓reduceIte]
            iframe Happl Hwok' HRD He HKV Hwt Hcp HFSE HSpT HRS Hhk
            isplitr
            · iunfold entryRegd at Hreg
              ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
              iexact Hr1
            isplitr
            · ipureintro; exact Hlgnn
            iframe Hst Happ Hbe HcF
            ipureintro; exact ⟨hpre, hdec, hid, hrq', HaOn ▸ hdk⟩
          have hkeep := applyStep_keep rq true x x' out hp hw Hstep0.1
          have hc' := hkeep.2
          have hmod : (sa, x'.log) = kvEntryOn γr.kv.c0 x.chain (sa, x.log) m := by
            rw [hkeepM, hkeep.1]
          have Htie : authTie sa rq out := authTie_nonKV sa rq out hkv'
          ihave HFS : srvFS s $$ [HFS]
          · rw [← HEo.1]; iexact HFS
          rw [srvRest_apply E γr A m rq true x x' out Htyp hdata hdec HkA.2 hp Hstep0.1]
          ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpaceOn rq x x' ar out hp Hch Hstep0.1
            $$ Hev HRes
          tail_on sa
      · -- an admin request: the auth row's admin steps (`adminEntryOn`)
        have hna := adminKindOk_needAdmin rq hadm
        obtain ⟨hkv', hfl⟩ := adminKindOk_kinds rq hadm
        icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %hs, #Hasf, #Hlend,
          #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
        ihave #HUA := srv_uberAuthStepsL_at hUA hRA hUGR hRGP hAE hApplyL hApply s ua E γa stl bel T hM
          $$ []
        · isplitr
          · iPkgInit
          iframe Hb Hasf Hsteps
        (try wp_auto)
        wp_apply hAd fv.lg e m ua fv.w true E
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot γa stl
            bel T sa _ hM hna hns $$ [Hst Happ Hbe HKV HRD Hfu Htie HT Htp HRS Hlc Hhk]
            as %ar %id ⟨HRD, Hout, #Har, HTr, %Hid, %x', %out, HKV, %Hstep0, HRes, #Hdel, -, HNS,
              HRS, HT, Htp, %hs', %sa', Hfu, Htie, %Hsa'⟩
        · simp only [↓reduceIte]
          iframe HUA Hwok' HRD He HKV HT Htp Hwba Hlend HRS Hlc Hhk
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          isplitr
          · ipureintro; exact Hlgnn
          iframe Hst Happ Hbe
          isplitr
          · ipureintro; exact hpre
          isplitr
          · ipureintro; exact ⟨hdec, hid, hadm, HaOn ▸ hdk, Hrb⟩
          isplitr
          · ipureintro; rw [Hch, hAuthOn]; rfl
          iexists hs; iframe Hfu Htie; ipureintro; exact Hhl
        obtain ⟨Hstep, hl', hc'⟩ := Hstep0
        have Hstep0 : apply.applyStep rq true x x' out ∧ apply.applyFloorOk rq true F x.log out :=
          ⟨Hstep, applyFloorOk_nonFloor rq true F x.log out hfl⟩
        have hR : adminStateR rq sa sa' := by simpa using Hsa'.2
        have hmod : (sa', x'.log) = kvEntryOn γr.kv.c0 x.chain (sa, x.log) m := by
          rw [hl']
          exact outcomeOn_eq γr.kv.c0 x.chain (sa, x.log) (sa', x.log) m Hdet
            (outcomeOn_of_adminStateR γr.kv.c0 x.chain (sa, x.log) m rq sa' Htyp hdata hdec hv hna hR)
        have Htie : authTie sa rq out := authTie_nonKV sa rq out hkv'
        ihave HAR := Hcl $$ %hs' %sa' Hfu Htie %Hsa'.1 HT Htp
        ihave HRS : srvRest E γr (A ++ [m]) $$ [HRS]
        · rw [srvRest_admin E γr A m rq Htyp hdata hdec hadm]; iunfold srvRest; iexact HRS
        ihave #Hnn : iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
            structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
            notNoSpaceErr err) $$ [HNS]
        · iexact HNS
        tail_on sa'

end proof

end EtcdGrove
end Perennial
