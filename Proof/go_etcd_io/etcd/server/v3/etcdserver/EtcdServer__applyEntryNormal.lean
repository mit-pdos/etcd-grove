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
  iframe Hbe Hlr
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
  iframe Hbe Hlr
  (try simp only [↓reduceIte])
  iframe Happ
  iexists m.index
  have hfin : stLoaded γ ⟨m.index, m.index, m.index, false⟩ =
      ({ k := m.index, p := m.index, eff := m.index, pending := false } : ApplyState) := by
    unfold stLoaded; rw [ite_eq_right hi0]
  rw [hfin] at *
  iexact Hst))

set_option hygiene false in
/-- The deferred update in either state. -/
local macro "tail_any" : tactic => `(tactic| (
  rcases hst1 with rfl | rfl
  · tail_done
  · tail_skip))

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
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM b e m st v3
  wp_start as ⟨#Hsrv, #He, Hst, Hbe, Hlr, %Hp, Hv3⟩
  wp_apply wp_with_defer as %defer defer
  iunfold isServer at Hsrv
  icases Hsrv with ⟨#Hsci, ⟨%fv, #Hfv⟩, #Hat⟩
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, #Hua, #Happl, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hq,
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
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr
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
        iframe Hbe Hst Hlr
    · -- data: the applier, with nothing to write (`ApplyV2storeOnly`)
      wp_apply hA fv.lg e m fv.ua fv.w false (batchLockInv γ TM) iprop(True) iprop(True)
        iprop(True) fv.hook $$ [] as %ar %id ⟨-, #Har⟩
      · iframe Happl He
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitl <;> itrivial
      (try wp_auto)
      iapply HΦ
      iframe Hbe Hst Hlr
  · -- the entry `i = p + 1`, above `ci`
    simp only [↓reduceIte]
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
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
      wp_apply hA fv.lg e m fv.ua fv.w true (batchLockInv γ TM)
        iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
        iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b)
        iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b)
        fv.hook $$ [Hst Happ Hbe] as %ar %id ⟨Hout, #Har⟩
      · iframe Happl He
        simp only [↓reduceIte]
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
          ipureintro; exact hpre
      ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
      · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
        · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
        · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
          imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
      imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        tail_any
      iunfold resultOk at Har
      icases Har with (%Hnull | ⟨%err, #Herr, #HerrIs⟩)
      · exact absurd Hnull Hif
      ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Perrs
      icases Hei with ⟨%ens, #Hens, %Hensp⟩
      (try wp_auto)
      iunfold applyErrIs at HerrIs
      ihave ⟨%S, %M, #Htree, %HS⟩ := HerrIs $$ %(GoInterface.ok ens)
      wp_apply hIs S M err (GoInterface.ok ens) (fun tii h => by cases h; exact Hensp) HS.2
        $$ [$Htree] as %isns -
      · ipureintro; exact HS.1
      iunfold waitOk at Hwok
      icases Hwok with ⟨%wi, %Hwi, #HTrig, -⟩
      cases isns
      · -- not `ErrNoSpace`: hand the result to the waiter
        (try wp_auto)
        rw [Hwi]
        (try wp_auto)
        (try dsimp only)
        ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
        wp_apply HT
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
          wp_apply HT
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
          wp_apply hGA s _
          (try wp_auto)
          tail_any

end proof

end EtcdGrove
end Perennial
