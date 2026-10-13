/-
Proof of `Spec/EtcdServer__applyEntryNormal.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AlarmContract

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  iframe Hbe Hlr Hgr HKV
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
  iframe Hbe Hlr Hgr HKV
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
  icases HR with ⟨%d', %rq', #Hcl', %Hp'⟩
  obtain ⟨hd', hΨ⟩ := Hp'
  subst hΨ
  ihave %Hdd := idClaim_agree' ρ.ids id d' m.data $$ Hcl' Hcl0
  subst Hdd
  rw [hdec] at hd'
  cases hd'
  iunfold resultΨ
  iexists ar
  isplitr
  · ipureintro; rfl
  iunfold resultIs
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert
  ipureintro; exact Hstep))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise: every expectation registered under the entry's id is the
proposer's `resultΨ` of the entry's request (the claims agree), which the result meets. -/
local macro "trig" : tactic => `(tactic| (
  iright
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitR at HR
  icases HR with ⟨%d', %rq', #Hcl', %Hp'⟩
  obtain ⟨hd', hΨ⟩ := Hp'
  subst hΨ
  ihave %Hdd := idClaim_agree' ρ.ids id d' m.data $$ Hcl' Hcl0
  subst Hdd
  rw [hdec] at hd'
  cases hd'
  iunfold resultΨ
  iexists ar
  isplitr
  · ipureintro; rfl
  iunfold resultIs
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert
  ipureintro; exact Hstep))

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
  intro s γ ci TM E ρ b e m st v3 x γr
  wp_start as ⟨#Hsrv, #Hewo, #He, Hst, Hbe, Hlr, Hgr, HKV, %Hpo, Hv3⟩
  obtain ⟨Hp, Hok, Htyp⟩ := Hpo
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv0 := Hsrv
  iunfold isServer at Hsrv
  icases Hsrv with ⟨#Hsci, ⟨%fv, #Hfv⟩, #Hat⟩
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, #Hua, #Happl, %HE, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hq,
    #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave #He' := He
  iunfold entryAt at He'
  icases He' with ⟨%Hnn, %pt, %pi, %pty, %d, #Hft, #Hpt, #Hfi, #Hpi, #Hfty, #Hpty, #Hfd, #Hds⟩
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
  icases Hlok with ⟨%li, %Hli, #HPromote⟩
  cases v3
  · -- replayed: no backend writes, state unchanged
    wp_auto
    wp_if_destruct
    · -- no data
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E x' ∗
          ⌜entryStep m false x x' out⌝) $$ [HKV]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV
        ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr HKV
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
        iframe Hbe Hst Hlr Hgr HKV
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
      icases HKV with ⟨%ua', #Hua', HKV, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hua Hua' gives %Hueq
      subst Hueq
      icombine Hw Hw' gives %Hweq
      subst Hweq
      wp_apply hA fv.lg e m fv.ua fv.w false E iprop(True) iprop(True) iprop(True) x rq id0 RD
        $$ [HKV HRD] as %ar %id ⟨HRD, -, #Har, %Hid, %x', %out, HKV, %Hstep, -⟩
      · iframe Happl Hwok' HRD He HKV
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · ipureintro; exact Hlgnn
        isplitr
        · itrivial
        ipureintro; exact ⟨hdec, hid, hrq, hdk⟩
      (try wp_auto)
      iapply HΦ
      iframe Hbe Hst Hlr Hgr
      iexists x', out
      isplitl
      · iunfold srvApplyKV; iexists fv.ua; isplitr; · iexact Hua
        isplitl [HKV]; · iexact HKV
        iexists fv.w, RD; iframe Hw Hwok' HRD
      · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
  · -- the entry `i = p + 1`, above `ci`
    simp only [↓reduceIte]
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E x' ∗
          ⌜entryStep m true x x' out⌝) $$ [HKV]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV
        ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
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
      icases HKV with ⟨%ua', #Hua', HKV, %w', %RD, #Hw', #Hwok', HRD⟩
      icombine Hua Hua' gives %Hueq
      subst Hueq
      icombine Hw Hw' gives %Hweq
      subst Hweq
      obtain ⟨HEP, HEf⟩ := HE
      wp_apply hA fv.lg e m fv.ua fv.w true E
        iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
        iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b)
        iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b) x rq id0 RD
        $$ [Hst Happ Hbe HKV HRD] as %ar %id ⟨HRD, Hout, #Har, %Hid, %x', %out, HKV, %Hstep, HRes⟩
      · iframe Happl Hwok' HRD He HKV
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
            icases Hdone with ⟨%mm, Hmt, HTM⟩
            imodintro
            iframe Happ Hbe
            isplitl [Hmt HTM Htok]
            · iunfold batchLockInv; iexists mm; iframe
            iexact Hst
        · iframe Hst Happ Hbe
          ipureintro; exact ⟨hpre, hdec, hid, hrq, hdk⟩
      ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
      · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
        · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
        · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
          imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
      imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
      ihave ⟨HKV, #Hcert⟩ := applyKV_idxCert E fv.ua x' $$ HKV
      ihave HKV : iprop(∃ (x'' : apply.ApplyKV) (out' : apply.ApplyOut), srvApplyKV s E x'' ∗
          ⌜entryStep m true x x'' out'⌝) $$ [HKV HRD]
      · iexists x', out
        isplitl
        · iunfold srvApplyKV; iexists fv.ua; isplitr; · iexact Hua
          isplitl [HKV]; · iexact HKV
          iexists fv.w, RD; iframe Hw Hwok' HRD
        · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
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
      icases Hei with ⟨%ens, #Hens, %Hensp⟩
      (try wp_auto)
      ihave #HerrT := applyErrIs_tree err $$ HerrIs
      ihave ⟨%S, %M, #Htree, %HS⟩ := HerrT $$ %(GoInterface.ok ens)
      wp_apply hIs S M err (GoInterface.ok ens) (fun tii h => by cases h; exact Hensp)
        (HS.2 (fun tii h => by cases h; exact Hensp))
        $$ [$Htree] as %isns -
      · ipureintro; exact HS.1
      iunfold waitInv at Hwok
      icases Hwok with ⟨%RD0, Hwok⟩
      iunfold isWait at Hwok
      icases Hwok with ⟨%wi, %Hwi, -, #HTrig, -⟩
      subst Hid
      ihave #Hcl0 : iprop(idClaim ρ.ids id m.data) $$ []
      · have he : entryWaitOk ρ E m = iprop(∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              idClaim ρ.ids id m.data) := by unfold entryWaitOk; rw [ite_eq_left Htyp]
        rw [he]
        iapply Hewo
        ipureintro; exact ⟨hdata, hdec, hid⟩
      cases isns
      · -- not `ErrNoSpace`: hand the result to the waiter
        (try wp_auto)
        rw [Hwi]
        (try wp_auto)
        (try dsimp only)
        ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
        wp_apply HT $$ [HRes]
        · trig
        (try wp_auto)
        tail_any
      · -- `ErrNoSpace`: raise the alarm unless it is raised already
        (try wp_auto)
        wp_apply hAG fv.alarmStore _ as %sl -
        · iexact Halm
        wp_if_destruct
        · -- raised already: hand the result to the waiter
          rw [Hwi]
          (try wp_auto)
          (try dsimp only)
          ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
            go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
          wp_apply HT $$ [HRes]
          · trig
          (try wp_auto)
          tail_any
        · wp_apply hLg s fv.lg $$ [Hlr] as ⟨%Hlg0, Hlr⟩
          · iframe Hlg Hlr; ipureintro; exact Hlgnn
          (try wp_auto)
          wp_apply hZI _ _ as %f1 -
          wp_apply hHB _ as %qs -
          wp_apply hZS _ _ as %f2 -
          (try wp_auto)
          wp_apply hZE _ as %f3 -
          (try wp_auto)
          wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2, f3]
          isplitr
          · ipureintro; rfl
          iintro %fsl ⟨-, -⟩
          (try wp_auto)
          wp_apply hW fv.lg _ _ $$ []
          · ipureintro; exact Hlg0
          (try wp_auto)
          -- the alarm goroutine (`GoAttach`): it proposes the alarm (the trust-boundary
          -- contract `EtcdServer.raftRequestAlarm`, `AlarmContract.lean`) and hands the result to
          -- the waiter (the trigger's premise is its precondition)
          iunfold srvGoRes at Hgr
          icases Hgr with ⟨Hwr, Htok⟩
          iunfold srvWgReader at Hwr
          icases Hwr with ⟨%γg, #Hgok, Hrd⟩
          ihave #Hgok' := Hgok
          iunfold srvGoAttachOk at Hgok'
          icases Hgok' with ⟨%gch, %gc, -, -, -, -, -, #Hctx, -, -⟩
          ihave HTP : iprop(waitTrig (reqWaitR ρ.ids E) id (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)) $$ [HRes]
          · trig'
          ipersist s
          ipersist id
          ipersist ar
          wp_func_lits
          wp_apply hGA s _ iprop(waitTrig (reqWaitR ρ.ids E) id (interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)) $$ [Hrd Htok Hlr HTP]
            as ⟨Hgr, Hlr⟩
          · iframe Hlr HTP
            isplitl [Hrd Htok]
            · iunfold srvGoRes; iframe Htok; iunfold srvWgReader; iexists γg; iframe Hgok Hrd
            iintro !> %Φ' HTP HΦ'
            wp_auto
            wp_apply hMID s fv.memberID $$ []
            · iframe #
            wp_apply (EtcdServer.raftRequestAlarm.wp_proof s γ ci TM E ρ γr gc «$a1_ptr») $$ [«$a1»]
              as %resp %err' -
            · iframe #; iexists _; iexact «$a1»
            (try wp_auto)
            rw [Hwi]
            (try wp_auto)
            (try dsimp only)
            ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
              go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
            wp_apply HT $$ [HTP]
            · iright; iexact HTP
            (try wp_auto)
            iapply HΦ'
            itrivial
          (try wp_auto)
          tail_any

end proof

end EtcdGrove
end Perennial
