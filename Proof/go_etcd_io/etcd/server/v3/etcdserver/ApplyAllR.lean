/-
**`applyAll` on a batch, in restart form** (R2d'a A5, 2026-11-06; DRAFT, nothing frozen:
`notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", "R2d'a Draft"). Lean-first (no Rocq
counterpart).

* `applyEntries.specBatchR`: `applyEntries.specBatch` over the restart point `rp` and Go's log `A`
  (the ghost rows at `ghostOf rp A`), in the environment's auth mode; `wp_proofBatchR` from the
  auth-off form `specBatchROff` (`ApplyEntriesR.lean`) and the auth-on form `specBatchROnC`
  (`ApplyEntriesROn.lean`, over `apply.specROn`).
* `applyAll.wp_proofBatchR`: `RunR.lean`'s `applyAll.specBatchR`, lean's `wp_proofBatch` over
  `applyEntries.specBatchR`. Go's rows (`ep.appliedi`, the snapshot state, the trigger, the disk
  snapshot) are lean's; the ghost rows go through. The merged-send branch (`server.go:1018-1023` at
  the pin `673da07c8`) is lean's once the window has closed after the batch; while it is left,
  `winNoMergedSendR` refutes the branch's guard `m.GetTerm() == apply.raftTerm` for this member's
  `MsgSnap` (`isServerApplyAll`'s member id, A7).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyEntriesR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyEntriesROn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplySnapshotR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyEntries(ep, ap)` at a restart point, in the modes `P`** (R2d'a A5, DRAFT):
`applyEntries.specBatch` (`server.go:1215-1239` at the pin `673da07c8`) with the ghost rows (the
applied index `g`, the KV model, the view, `epCsAt`, `srvApRes`) at `ghostOf rp A`, the rest buckets
`srvRestR` and the batch `kvBatchR`; Go's rows (`ep.appliedi`, `ep.appliedt`, `loopOk`) at `A`. -/
abbrev EtcdServer.applyEntries.specBatchRAt (P : auth.AuthMode → Prop) : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (rp : RestartPt) (A : List EntryModel) (γp : WTNames)
    (dv : Option Loc) (w : Nat) (g : w64) (sa : auth.AuthState),
  P E.authMode → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeM E.authOn E.lm (unapplied ai ms) →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (g + 1) (unapplied ai ms) →
  uint.Z g = uint.Z γr.raft.ai0 + (ghostOf rp A).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      epCsAt ρ.raft (ghostOf rp A) cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr g ∗ appliedLogAt γr g x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗ srvRestR E γr rp A ∗
      kvBatchR γr (ciEff γ st.k) ai rp A (unapplied ai ms) ∗
      dvView ρ.raft dv (ghostOf rp A) ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (ghostOf rp A) ∗ srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ unapplied ai ms)) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (ghostOf rp (A ++ unapplied ai ms)) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc) (g' : w64),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai ms)) cs' ∗
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr g' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr g' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp (A ++ unapplied ai ms)) x' sa' ∗
          srvRestR E γr rp (A ++ unapplied ai ms)) ∗
        ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ unapplied ai ms)).length ∧
          loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          termAfter at0 (unapplied ai ms) at'⌝ }}

/-- **`applyEntries.specBatchR`** (R2d'a A5, DRAFT): in either auth mode (`.any` excluded). -/
abbrev EtcdServer.applyEntries.specBatchR : Prop :=
  EtcdServer.applyEntries.specBatchRAt (GF := GF) (hG := hG) (· ≠ .any)

/-- **`applyEntries.specBatchROn`** (R2d'a A5, DRAFT): with auth on; `specBatchROnC`
(`ApplyEntriesROn.lean`) in the mode-indexed form. -/
abbrev EtcdServer.applyEntries.specBatchROn : Prop :=
  EtcdServer.applyEntries.specBatchRAt (GF := GF) (hG := hG) (fun m => ∃ γa, m = .on γa)

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `applyAll.specBatchR`'s running token is `srvRunH`. -/
theorem srvRunH_applyAll_specBatchR (γs : ServerRaftNames) (dv : Option Loc) :
    _root_.Perennial.EtcdGrove.EtcdServer.applyAll.specBatchR.match_1 (fun _ => IProp GF) dv
      (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH γs dv := by
  cases dv <;> rfl

/-- **`applyEntries.specBatchR`** (R2d'a A5, DRAFT): `wp_proofBatchROff` with auth off,
`wp_proofBatchROnC` with auth on (`applyEntries.wp_proofBatch`'s split). -/
theorem EtcdServer.applyEntries.wp_proofBatchR
    (hOff : EtcdServer.applyEntries.specBatchROff (GF := GF) (hG := hG))
    (hOn : EtcdServer.applyEntries.specBatchROnC (GF := GF) (hG := hG)) :
    EtcdServer.applyEntries.specBatchR (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g sa hany hRB Hms
    Hai1 Hok hEok hdv hg0
  cases hm : E.authMode with
  | any => exact absurd hm hany
  | on γa =>
    have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hm]; rfl
    rw [hon] at hEok ⊢
    simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true]
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hlnil, Hbw, Hes, Hrac, Hesl, Hentsat, Hai, Hat, Hcs, Hcv, Hst, Hbe, Happ,
      Hlr, Hgr, HKV, Hao, Hlog, Hbc, HW, HWA, Hfs, Hka, HRS, Hkb, Hdv, Hdvr, Hrun, HAR, HtokR⟩ HΦ
    iapply (hOn s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g γa sa hm
      (hRB hon) Hms Hai1 Hok hEok hdv) $$ [Hbw Hes Hrac Hesl Hentsat Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr
      HKV Hao Hlog Hbc HW HWA Hfs Hka HRS Hkb Hdv Hdvr Hrun HAR HtokR] [HΦ]
    · iframe Hpkg Hsrv Hlnil Hbw Hes Hrac Hesl Hentsat Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hlog
        Hbc HW HWA Hfs Hka HRS Hkb Hdv Hdvr Hrun HAR HtokR
      ipureintro; exact hg0
    iintro !> ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', %g', Hai, Hat, Hcs, Hcv, Hst,
      HtokR, Hbe, Hci, Hlr, Hgr, Hao, HWT, ⟨%x', %sa', HKV, %Hstep, Hlog, Hka, HRS⟩, %Hp⟩
    iapply HΦ
    iframe Hfs Hdv Hrun HAR
    iexists st', ai', at', a', t', cs', g'
    iframe Hai Hat Hcs Hcv Hst HtokR Hbe Hci Hlr Hgr Hao HWT
    isplitl [HKV Hlog Hka HRS]
    · iexists x', sa'; iframe HKV Hlog Hka HRS; ipureintro; exact Hstep
    ipureintro; exact Hp
  | off =>
    have hoff : E.authOn = false := by rw [apply.AEnv.authOn_eq, hm]; rfl
    have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
      intro k; unfold srvTokRights; rw [hm]
    rw [hoff] at hEok ⊢
    simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false, hT]
    iintro %Φ ⟨#Hpkg, #Hsrv, -, Hbw, Hes, Hrac, Hesl, Hentsat, Hai, Hat, Hcs, Hcv, Hst, Hbe, Happ, Hlr,
      Hgr, HKV, Hao, Hlog, Hbc, HW, HWA, Hfs, Hka, HRS, Hkb, Hdv, Hdvr, Hrun, HAR, -⟩ HΦ
    iapply (hOff s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g Hms Hai1
      Hok hEok hdv) $$ [Hbw Hes Hrac Hesl Hentsat Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hlog Hbc HW
      HWA Hfs Hka HRS Hkb Hdv Hdvr Hrun HAR] [HΦ]
    · iframe Hpkg Hsrv Hbw Hes Hrac Hesl Hentsat Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hlog Hbc HW
        HWA Hfs Hka HRS Hkb Hdv Hdvr Hrun HAR
      ipureintro; exact hg0
    iintro !> ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', %g', Hai, Hat, Hcs, Hcv, Hst,
      Hbe, Hci, Hlr, Hgr, Hao, HWT, ⟨%x', HKV, %Hstep, Hlog, Hka, HRS⟩, %Hp⟩
    iapply HΦ
    iframe Hfs Hdv Hrun HAR
    iexists st', ai', at', a', t', cs', g'
    iframe Hai Hat Hcs Hcv Hst Hbe Hci Hlr Hgr Hao HWT
    isplitl [HKV Hlog Hka HRS]
    · iexists x', sa; iframe HKV Hlog Hka HRS; ipureintro; exact Hstep
    ipureintro; exact Hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`applyAll.specBatchR`** (R2d'a A5, DRAFT; `RunR.lean`'s hypothesis): lean's `wp_proofBatch`
over `applyEntries.specBatchR`, the merged send refuted while a window is left
(`winNoMergedSendR`). -/
theorem EtcdServer.applyAll.wp_proofBatchR
    (hASnap : EtcdServer.applySnapshot.spec (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specBatchR (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG))
    -- (2026-10-31, S1) the merge branch: the message's getters, the merge, the send, and what
    -- the snapshot window takes (`mergedCreate_window`)
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hGS : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (hGM : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    (hC : mvcc.store.Commit.spec (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specBatchR (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr b ep ap es ents ms f0 rac nc st ai at0 a t cs x sa A mst γs γp dv γnc w nk
    q γn rt n rp g T
  simp only [srvRunH_applyAll_specBatchR]
  wp_start as ⟨%hP, #HsrvC, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, #Hesl, #Hentsat, Hai, Hat, Hcs, #Hcv,
    Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, HKV, Hao, #Hlog, #Hbc, #HW, #HWA, Hka, HRS, #Hkb, #Hwin, HT, #Hbagn, Hdv, #Hdvr, HAR, Hrun, #Hsd, #Hkv, #Hmsi, HwalT, #Hrtf, #Hrt, Hso, HtokR⟩
  obtain ⟨hM, hRB, Hms, Hai1, Hok, hEok, hdv, hAL, hAT, Hdisk, hciA, hcia, hg0, hγn, hpre, hnA⟩ := hP
  have hon : E.authOn = C.isOn := by rw [apply.AEnv.authOn_eq, hM, AuthC.mode_isOn]
  -- (the auth component's stage 2c) the slot's rows at the mode's
  ihave #Hsrv := (isServerM_C C s γ ci TM E ρ γr).2 $$ HsrvC
  ihave #HlnilM : srvLessorNilM C.isOn s $$ []
  · rw [srvLessorNilM_eq]; iexact Hlnil
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x sa).2 $$ HKV
  ihave HtokR : srvTokRights E (ciEff γ st.k) $$ [HtokR]
  · rw [srvTokRights_eq C E _ hM]; iexact HtokR
  icases srvApRes_cfg_size s γr (ghostOf rp A) $$ HAR with ⟨HAR, %hsz⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%sv, #Hfl⟩, -, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, %Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, -, #Hsc,
    ⟨%stg, #Hstgf, #Hstgc⟩, -, #Hinf, -, ⟨%tr, %γN, %lid, %SN, %TSN, #Htrf, #Htr, %HγN⟩, %Hkv0⟩
  ihave #HstgS := Hstgc
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%gI, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  -- (R2d'a) the batch's window facts (`kvBatchR`): Go's start index `ai₀ = 0`, the backend's log
  -- through the consistent index
  ihave #HkbR := Hkb
  iunfold kvBatchR at HkbR
  icases HkbR with ⟨-, -, %HkbP⟩
  obtain ⟨HkAi, -, HkA0, -, -, -⟩ := HkbP
  have hGl : ∀ G : List EntryModel, ((ghostOf rp G).length : Int) =
      G.length + (rp.A₀.length - G.length : Nat) := by
    intro G; rw [ghostOf_length]; push_cast; rfl
  wp_auto
  -- `s.applySnapshot(ep, apply)`: no snapshot
  wp_apply hASnap.1 s ep ap $$ []
  · iframe #
  (try wp_auto)
  -- `s.applyEntries(ep, apply)`, lending it `forceDiskSnapshot` (D14i)
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  have hAE1 := hAE s γ ci TM E ρ b ep ap es ents ms f0 rac st ai at0 a t cs x γr rp A γp dv w g sa
    (by rw [hM]; cases C <;> simp [AuthC.mode])
    (fun h => by rw [hon] at h; cases C <;> simp_all [AuthC.isOn, acReceiptOk]) Hms Hai1 Hok
    (by rw [hon]; exact hEok) hdv hg0
  rw [hon] at hAE1
  wp_apply hAE1
    $$ [Hai Hat Hcs Hcv Hst Hbe Happ Hlr Hgr HKV Hao Hfs Hka HRS Hdv Hrun HAR HtokR]
    as ⟨Hfs, Hdv, Hrun, HAR, %st', %ai', %at', %a', %t', %cs', %g', Hai, Hat, Hcs, #Hcv', Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hao, #HWA',
      ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  · iframe #; iframe
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  obtain ⟨hg', hok', hai', hlen', hci', hat'⟩ := Hpost
  -- (R2d'a) the ghost index after the batch: at least Go's, at most the new consistent index
  have hgA := hGl A
  have hgB := hGl (A ++ unapplied ai ms)
  have hlAB : ((A ++ unapplied ai ms).length : Int) = A.length + (unapplied ai ms).length := by
    simp
  have hag : uint.Z ai' ≤ uint.Z g' := by omega
  have hciL0 : uint.Z ai' ≤ uint.Z (ciEff γ st'.k) := by
    rcases hci' with ⟨hun, hc⟩ | hc
    · rw [hun, List.length_nil] at hlen'; rw [hc]; omega
    · rw [hc]; omega
  have hciL : uint.Z g ≤ uint.Z (ciEff γ st.k) → uint.Z g' ≤ uint.Z (ciEff γ st'.k) := by
    intro h
    rcases hci' with ⟨hun, hc⟩ | hc
    · have hgg : g' = g := by
        have : A ++ unapplied ai ms = A := by rw [hun, List.append_nil]
        rw [this] at hg'; word
      rw [hc, hgg]; exact h
    · rw [hc]; omega
  have Hai' : uint.Z ai ≤ uint.Z ai' := by rw [hai']; exact Int.le_max_left _ _
  -- (D22 J1b) the snapshot resources at the new applied index
  ihave Hso := srvSnapOwn_mono s ci E γr _ ai ai' Hai' $$ Hso
  ihave Hss : srvSnapState s ep mst γs ai' (W64 0) $$ [Hsd0 Hsm0 Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd0 Hsm0 Hsf1 Hmst Hslb0
    ipureintro; exact ⟨by have := Hdm0.1; omega, by have := Hdm0.2; omega⟩
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, -⟩
  · iframe #; iframe Hbr
  wp_apply hLg s sv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hV be sv.lg true bsl
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the waiters through `ai'`
  icases srvAppliedOwn_lb γr g' $$ Hao with ⟨Hao, #Hlbg⟩
  ihave #Hlb : appliedAtLeast γr ai' $$ []
  · iunfold appliedAtLeast; iunfold appliedAtLeast at Hlbg
    iapply (monoNatLbOwn_le (GF := GF) (uint.nat ai') (by word)) $$ Hlbg
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`: (D43 M3) the view after the batch deposited
  wp_apply wp_notify_receive γnc nc _ $$ [Hnrc Hdv]
  · iframe Hncb Hnrc Hdv
  (try wp_auto)
  -- (D19i part 1) `select { case <-apply.raftAdvancedC: case <-s.stopping: return }`: raft has
  -- advanced past the batch, or the server stops (no snapshot)
  iunfold rnAdvChan at Hracc
  icases Hracc with ⟨%γac, #Hracc⟩
  iunfold stopChan at Hstgc
  icases Hstgc with ⟨%γsg, #Hstgc⟩
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  rotate_left
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstgc
      iapply stop_chan_receive _ _ _ _ _ $$ Hstgc
      iintro ⟨-, -⟩
      (try wp_auto)
      ihave HtokR : acTok C (ciEff γ st'.k) $$ [HtokR]
      · rw [← srvTokRights_eq C E _ hM]; iexact HtokR
      ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
      iapply HΦ
      iexists γ, TM, E, b, st', ai', at', a', t', cs', g'
      iframe HsrvC Hlnil
      isplitr
      · ipureintro; exact beSucc_refl γ E
      iframe HT Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
      isplitl [Hao]
      · iexact Hao
      isplitr
      · iexact Hlbg
      isplitr
      · iexact HWA'
      isplitl [HKV Hka HRS]
      · iexists x', sa'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
      isplitr
      · iexact Hkv
      isplitl [HwalT]
      · iexact HwalT
      isplitl [Hso]
      · iexact Hso
      ipureintro; exact ⟨hg', hok', hai', hci'.imp_left And.right, hciL, hat'⟩
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ileft
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rac, γac
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownStopChan_is_chan $$ Hracc
  iapply stop_chan_receive _ _ _ _ _ $$ Hracc
  iintro ⟨#Hadv, -⟩
  (try wp_auto)
  -- (#11) what the snapshot takes: `raftAdvancedC`'s payload (the node's applied index and the
  -- storage's past `ai'`, the batch's entries frozen with their terms), the log invariant
  -- (`raftPropose`'s), the batch's committed log (`kvBatch`'s), `ep.confState` the voters'
  have hρr : ρ.raft = γr.raft := by rw [← Hρrd]
  have hidx : (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat =
      uint.nat ai' := by rw [← hai']; word
  have hlenA : uint.nat ai' = (A ++ unapplied ai ms).length := by
    rw [List.length_append]; have := hlen'; have := hAL; word
  have hltA : lastTermIs (A ++ unapplied ai ms) at' := lastTermIs_append hAT hat'
  icases Hadv with ⟨#Hnal, #Hsdl, -, #Hfts, #Hwh⟩
  ihave #Hnal' : (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nk (uint.nat ai')) $$ []
  · rw [← hidx, ← hρr]; iexact Hnal
  ihave #Hwh' : rnWalHanded γn (uint.nat ai') $$ []
  · rw [← hidx]; iexact Hwh
  ihave #HrnS' := HrnS
  iunfold srvRaftNode at HrnS'
  icases HrnS' with ⟨%rn0, -, HrpS⟩
  iunfold raftPropose at HrpS
  icases HrpS with ⟨%rni0, -, #Hrli, -⟩
  ihave #Hkb' := Hkb
  iunfold kvBatchR at Hkb'
  icases Hkb' with ⟨#HlbB, -, -⟩
  ihave Hstor : srvSnapStor mst γs γr nk ai' at' $$ []
  · iunfold srvSnapStor
    iframe Hmsi
    isplitr
    · rw [← hidx, ← hρr]; iexact Hsdl
    isplitr
    · rw [← hρr]; iexact Hrli
    iexists A ++ unapplied ai ms
    iframe HlbB
    ipureintro; exact ⟨by rw [← hlenA]; try word, hltA⟩
  ihave ⟨#Hfz, #Hft⟩ := srv_frozen_of_terms γs (A ++ unapplied ai ms) ai' at' hlenA hltA $$ Hfts
  ihave #Hecs : iprop(⌜uint.Z ai' = 0⌝ ∨ epCsCfg γr cs') $$ []
  · by_cases hL : A ++ unapplied ai ms = []
    · ileft; ipureintro
      have h0 := congrArg List.length hL
      simp only [List.length_nil] at h0
      rw [h0] at hlenA; word
    · iright; iunfold epCsCfg; rw [← hρr]
      iapply epCsAt_ne _ _ _ (by unfold ghostOf; exact List.append_ne_nil_of_left_ne_nil hL _) $$ Hcv'
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`
  have hS1 := hSINC.1 s E ρ.wait γ ci b γr ep st' ai' at' cs' a' t' x' mst γs nk γp
    (w + (unapplied ai ms).length) TM ρ sa' q γn
  rw [hon] at hS1
  wp_apply hS1 hok'
      hciL0 Hdisk.2.1.2.2.1 hsz Hdisk.2.2.1 hγn hpre
    $$ [Hss Hai Hat Hcs Hst Hbe Happ Hlr HKV HwalT Hstor]
    as ⟨%st'', Hss, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, HwalT, %Hst''⟩
  · iframe #; iframe
  (try wp_auto)
  ihave HKV := (srvApplyKVM_C C s E ρ.wait x' sa').1 $$ HKV
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- (2026-10-31, S1) the step's end, shared by the select's branches: the apply thread at a state
  -- `stF` of the same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ stF ai' ∧ ciEff γ stF.k = ciEff γ st'.k⌝ -∗
      epAppliedIAddr ep ↦ ai' -∗ epAppliedTAddr ep ↦ at' -∗ epConfStateAddr ep ↦ cs' -∗
      applyThread γ stF -∗ applyBackend γ ci b -∗ ciApplying ci a' t' -∗ srvLgReader s -∗
      srvGoRes s -∗ srvApplyKVC C s E ρ.wait x' sa' -∗
      kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (ghostOf rp (A ++ unapplied ai ms)) x' sa' -∗
      srvRestR E γr rp (A ++ unapplied ai ms) -∗ T -∗ Φ #()) $$ [HΦ Hss Hbr HAR Hrun Hao HwalT HtokR Hso]
  · iintro %stF %HF Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS HT
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    ihave HtokR : acTok C (ciEff γ stF.k) $$ [HtokR]
    · rw [HF.2, ← srvTokRights_eq C E _ hM]; iexact HtokR
    iapply HΦ
    iexists γ, TM, E, b, stF, ai', at', a', t', cs', g'
    iframe HsrvC Hlnil
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe HT Hai Hat Hcs Hcv' Hss Hst HtokR Hbe Happ Hlr Hgr Hbr HAR Hrun
    isplitl [Hao]
    · iexact Hao
    isplitr
    · iexact Hlbg
    isplitr
    · iexact HWA'
    isplitl [HKV Hka HRS]
    · iexists x', sa'; iframe HKV Hlog' Hka HRS; ipureintro; exact Hx'
    isplitr
    · iexact Hkv
    isplitl [HwalT]
    · iexact HwalT
    isplitl [Hso]
    · iexact Hso
    ipureintro
    exact ⟨hg', HF.1, hai', by rw [HF.2]; exact hci'.imp_left And.right, by rw [HF.2]; exact hciL,
      hat'⟩
  -- `select { case m := <-s.r.msgSnapC: ...; default: }` (2026-10-31, S1: a `MsgSnap` raft handed
  -- out, merged with the backend's image and sent when the guard holds)
  -- (R2d'a A10 item 5) the merged send's receive through the raft node's bag at the run's names
  -- `γn` (`srvSnapBagN`: its `MsgSnap`s above `γn.t0`), the same channel as `isServerApplyAll`'s
  iunfold srvSnapBagN at Hbagn
  icases Hbagn with ⟨#Hmidm, %msc', #Hmscf', #Hmscb⟩
  ihave %Hmsceq := typedPointsto_agree_wand _ _ _ _ _ $$ Hmscf Hmscf'
  subst Hmsceq
  iunfold isRNMsgSnapC at Hmscb
  icases Hmscb with ⟨%γc, #Hmscb⟩
  ihave #Hmscch := is_bag_is_chan γc msc _ $$ Hmscb
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hrli' : srvRaftLogInv γr.raft $$ []
  · rw [← hρr]; iexact Hrli
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hmscch
      unfold nonblockingRecvAu
      isplit
      · iapply chanBag_nbRecv γc msc _ _ $$ Hmscb
        iintro %m HP
        iunfold rnSnapMsg at HP
        icases HP with ⟨%sm, Hm, %Htyb, #Hsm, -⟩
        obtain ⟨Hty, Hsbt⟩ := Htyb
        rw [hγn]
        -- (R2d'a A7) past the window after the batch, or no merged send at the batch's term
        -- (`winNoMergedSendR`, this member's `MsgSnap`: `isServerApplyAll`'s member id)
        ihave ⟨%Hwt, Hm, HT⟩ : iprop(⌜rp.A₀.length ≤ (A ++ unapplied ai ms).length ∨ sm.msg.Term' ≠ rt⌝ ∗
            msgOwn m (DFrac.own 1) sm ∗ T) $$ [Hm HT]
        · iunfold winNoMergedSendR at Hwin
          icases Hwin with (%Hnil | #Hwin)
          · iframe Hm HT; ipureintro; left
            exact Nat.le_of_not_lt (fun h => by
              have := List.length_drop (l := rp.A₀) (i := (A ++ unapplied ai ms).length)
              rw [Hnil] at this; simp at this; omega)
          · rw [← hγn]
            by_cases hlt : uint.Z γn.t0 < uint.Z rt
            · ihave ⟨%Hn, Hm, HT⟩ := Hwin $$ %hlt HT %γn.id %m %sm Hmidm Hm Hsm
              iframe Hm HT; ipureintro; right; exact Hn Hty
            · -- `rt ≤ t0`: the bag's `MsgSnap` is above `t0` (`rnSnapMsg`'s bound)
              iframe Hm HT; ipureintro; right
              intro h; rw [h] at Hsbt; exact hlt Hsbt
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave %Hsnp := srv_sentSnap_pos γr γn.id sm sn Hty hsn $$ [Hrli' Hsm]
        · iframe Hrli' Hsm
        -- two Go steps' time receipts (`m`'s zero value, `GetTerm`'s method value), for the merge
        -- window's write tokens
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction _)) (Val _))
          wp_pure)
        wp_bind (App (Val (GoInstruction _)) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr1 Hl1
        iapply wp_value'
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          first | wp_pure | wp_load | wp_store | wp_alloc_auto)
        wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr2 Hl2
        iapply wp_value'
        (try wp_auto)
        wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
        · iframe #; iframe Hm
        (try wp_auto)
        wp_if_destruct
        · -- the batch's term: the snapshot's index
          try have HifT := Hif
          wp_apply (hGS.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as %ps ⟨Hsn, Hmb⟩
          · iframe #; iframe Hm
          rw [hsn]
          iunfold snapOpt at Hsn
          wp_apply (hGM.1 ps (DFrac.own 1) sn) $$ [Hsn] as %pm ⟨Hmd, Hsnb⟩
          · iframe #; iframe Hsn
          wp_apply (hGI pm (DFrac.own 1) sn.Metadata') $$ [Hmd] as Hmd
          · iframe #; iframe Hmd
          ihave Hsn := Hsnb $$ Hmd
          ihave Hm := Hmb $$ [Hsn]
          · iunfold snapOpt; iexact Hsn
          (try wp_auto)
          wp_if_destruct
          · -- the merge: the snapshot at most the applied index (the guard); past the window
            -- (`winNoMergedSendR`), so every ghost row Go's
            have HifI := Hif
            have hW : rp.A₀.length ≤ (A ++ unapplied ai ms).length :=
              Hwt.resolve_right (fun hn => hn (by
                first | rfl | exact HifT | exact HifT.symm | (simp at HifT; exact HifT)))
            have hgai : g' = ai' := by
              rw [ghostOf_past rp _ hW] at hg'
              simp only [List.length_append] at hg'; push_cast at hg'
              word
            ihave #Hlog'' : appliedLogAt γr ai' x'.log $$ []
            · rw [← hgai]; iexact Hlog'
            rw [ghostOf_past rp _ hW, srvRestR_past E γr rp _ hW]
            have hciE : ciEff γ st''.k = ai' := by
              rw [Hst''.2]
              have h2 : uint.Z (ciEff γ st'.k) ≤ uint.Z ai' := by
                rcases hci' with ⟨hun, hc⟩ | hc
                · rw [hun, List.length_nil] at hlen'; rw [hc]
                  have : (rp.A₀.length : Int) ≤ A.length := by
                    have := hW; rw [hun] at this; simp at this; exact_mod_cast this
                  omega
                · rw [hc]; omega
              word
            have hlenZ : uint.Z ai' = ((A ++ unapplied ai ms).length : Int) := by
              have := uint_nat_eq ai'; omega
            have hpos : 0 < uint.Z ai' := by word
            (try wp_auto)
            -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
            icases srvApplyKVC_coreA C s E ρ.wait x' sa' $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- the component lends its buckets to the window (none off)
            ihave HL := acRes_lend C s E ua sa' hM $$ HAr
            icases Hkv with ⟨%kv, #Hkvf, #Hkvi⟩
            imod mergedCreate_window hC hSnap hOn hSave hPut hUR hID hName hSafe C.isOn s γ ci TM E ρ
                γr b st'' ai' a' t' (A ++ unapplied ai ms) x' ρ.wait γp ua kv Hst''.1 hciE hpos hlenZ
                (acBkts C) (acImg C sa') (acRes C s E ua sa') (acBkts_rest C)
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 Hr2 Hl2 HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv Hkvf Hkvi HW Hlog'' HlbB Hr1 Hl1 Hr2 Hl2 Hst Hbe Happ HKVc HRS HL
            -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
            -- the snapshot's reader slot; the reader goroutine's fork token comes back
            iunfold srvGoRes at Hgr
            icases Hgr with ⟨HgrW, HthT⟩
            wp_apply (hCM s m sm at' ai' cs' sv.lg kv be dq RC RC' RS RS' _)
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HthT]
              as %mg ⟨Hlr, HRS', Hbeo, HthT, %rc, %D, %c, #Hmg, #Hml, #Hcso, Hrs, %HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HthT; ipureintro; exact Hlgnn
            ihave Hgr : srvGoRes s $$ [HgrW HthT]
            · iunfold srvGoRes; iframe HgrW HthT
            imod Hback $$ HRS' Hbeo with ⟨%st3, Hst, Hbe, Happ, HKVc, HRS, HAr, %Hst3⟩
            ihave HKV := HKVk $$ HKVc HAr
            icases srvApplyKVC_idxCert C s E ρ.wait x' sa' $$ HKV with ⟨HKV, #Hicx⟩
            ihave #Hrcx := mvcc.idxCert_rcpt E.γ.idx x'.log $$ Hicx
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) Hrt0
            ihave #Hecs' : epCsCfg γr cs' $$ []
            · icases Hecs with (%H0 | #H)
              · exfalso; omega
              · iexact H
            iunfold epCsCfg at Hecs'
            iunfold epCsVoters at Hecs'
            icases Hecs' with ⟨%c0, #Hc0, %Hcs0⟩
            ihave %Hcc := csOpt_agree cs' c c0 $$ [Hcso Hc0]
            · iframe Hcso Hc0
            subst Hcc
            ihave %h61 := srvFrozenTerm_bound γs ai' at' $$ Hft
            imod srv_merged_sent γr (A ++ unapplied ai ms) ai' at' c γn.id ct sm sn hpos h61 hsz hlenZ
                hltA Hcs0 Hty hsn (by word) (by have := hnA; have := uint_nat_eq ai'; omega)
              $$ [Hrli' HlbB Hsm Hct] with #Hsm'
            · iframe Hrli' HlbB Hsm Hct
            -- (`merged_imageC`) the image's certificate: the component's buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗
                □ (srvNet (GF := GF) γr.raft.raft).img ai' D $$ [Hka]
            · iapply (merged_imageC C s γ ci TM E ρ γr ai' (A ++ unapplied ai ms) x' sa' D hM hlenZ
                Hkv0)
              iframe Hsrv Hka Hrcx; ipureintro; exact HQd
            imod Hmi with ⟨Hka, #Himg⟩
            imod srvMerged_bundle γr.raft.raft m rc sm γn.id c ai' at' D Hty
              $$ [Hml Hsm' Hrs Himg] with Hbun
            · iframe Hml Hsm' Hrs Himg
            (try wp_auto)
            wp_apply (hSMS s mg m rc sv.lg sv.memberID stg tr γN SN TSN lid) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγN]; iframe Hbun; ipureintro; exact Hlgnn
            (try wp_auto)
            have hF3 : loopOk γ st3 ai' ∧ ciEff γ st3.k = ciEff γ st'.k :=
              ⟨Hst3.1, by rw [Hst3.2]; exact Hst''.2⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS HT
          · (try wp_auto)
            iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS HT
        · (try wp_auto)
          iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS HT
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st'' %Hst'' Hai Hat Hcs Hst Hbe Happ Hlr Hgr HKV Hka HRS HT

end proof

section recvR
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
open go_etcd_io.raft.v3

/-! ### The snapshot receive inside the window (R2d'a task 4, DRAFT)

`snapRecv_image(On)` with the rest buckets at an image `r0` of the applied log `A`'s table
(`srvRestRp E γr A r0`) whose members have the model's ids (`hids`; inside the window `r0` is
`restReplay`, `restReplay_memKeys`), through the ids form of `membership.clusterImageOk_restModel`.
The proofs are the frozen ones with the rest opened and closed by `srvRestRp_open`/`srvRestRp_close`. -/

/-- `srvRest_close` at an image `r` (`srvRestRp`). -/
theorem srvRestRp_close (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (r : apply.RestM) :
    (∃ f : w64 → w64, ⌜E.lg = true → leaseTTLsGeReq (appliedTable γr A) f⌝ ∗
      E.RO (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids) r) ∗
      apply.ltHalf E (srvIds E (appliedTable γr A).ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTable γr A) ∗ srvEver E A) ⊢
      srvRestRp E γr A r := by
  iintro ⟨%f, %Hf, H1, H2, H3, H4, HU⟩
  iapply (srvRestRp_eq_at E γr A r).2
  iframe HU
  iapply (srvRestAt_open E _ _).2
  iexists f
  iframe H1 H2 H3 H4
  ipureintro; exact Hf

/-- **`snapRecv_image` inside the window** (DRAFT): at an image `r0` with the model's ids. -/
theorem snapRecv_imageR (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (hkb : E.γ.kb = some d)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H)
    (r0 : apply.RestM)
    (hids : ∀ k, (r0.mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).mem !! k).isSome) :
    ⊢ srvKVInvs E γr -∗ srvImage γ i D -∗ kvApplied γr.raft γr.kv A x -∗ srvRestRp E γr A r0 -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvApplied γr.raft γr.kv A x ∗ srvRestRp E γr A r0 ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log) (r : mvcc.CmpRecs), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFacts γr d D cl i A A' x R r
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗
        mvcc.crevPermAt E.γ r.crev := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok, %Hcm, %Hlgk, #Hcp⟩
  have hdcm : d.cm = γr.kv.cmp := by
    have h2 := Hcm.2; rw [hkb] at h2; simp only [mvcc.kbCmpM] at h2
    rw [Hcm.1]; cases hd : d.cm <;> cases he : E.cmp <;> simp_all
  ihave #HkI0 : kvInv (GF := GF) ⟨γ, [], W64 0⟩ γr.kv $$ []
  · rw [← hraft]; iexact HkI
  ihave #HrI0 : srvRaftLogInv (GF := GF) ⟨γ, [], W64 0⟩ $$ []
  · rw [← hraft]; iexact HrI
  imod (dbImage_of_srvImage γ γr.kv i D hc0 hch hlog0) $$ HkI0 HrI0 Himg with #Hdb0
  ihave #Hdb : dbImage γr.raft γr.kv i D $$ []
  · rw [hraft]; iexact Hdb0
  iunfold dbImage at Hdb
  icases Hdb with ⟨%A', #HA', %hA', #Hrcp⟩
  obtain ⟨hlen', himA⟩ := hA'
  iunfold kvApplied at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedL at Hal
  icases Hal with ⟨#HA, Hhi, #Hc, %Hl⟩
  ihave %Hcmp := srvRLogLb_prefix γr.raft A A' $$ [HA HA']
  · iframe HA HA'
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [hai0, hz] at hai hlen'
  have hAA' : A <+: A' := by
    rcases Hcmp with h | h
    · exact h
    · have := h.length_le; omega
  imod kv_log_ccOk γr.raft γr.kv A' $$ HkI HrI HA' with %Hcc
  imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HA' with %Hpl0
  have Hpl : plainLogM γr.kv.cmp γr.kv.lm A' := Hpl0.1
  -- the cluster's in-memory members, from the rest resource (S2–S4 Probe: in either lease mode,
  -- `srvRestRp_open`; the records leave the members, `restLeasesWith_mem`)
  ihave ⟨%f, %Hf, Hrest, HL, HG, #HRq, HU⟩ := srvRestRp_open E γr A r0 $$ Hrest
  rw [hRO]
  iunfold srvRestOwnH at Hrest
  icases Hrest with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hrn, Hmem, %Hmi⟩
  rw [apply.restLeasesWith_mem]
  ihave #HA'' : srvRLogLb γr.raft (γr.raft.pre ++ A') $$ []
  · rw [hpre0, List.nil_append]; iexact HA'
  have hLL : γr.raft.pre ++ A <+: γr.raft.pre ++ A' := (List.prefix_append_right_inj _).2 hAA'
  have hbl : γr.raft.raft.boot.length ≤ (γr.raft.pre ++ A').length := by
    rw [hpre0, hrr, List.nil_append]; omega
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccBootOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_static _ _ (Hcc m hm ht)
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' _ hids $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  have hsplit := kvModel_split γr.kv A' hlog0
  obtain ⟨⟨r, hkI, hr⟩, hci, htm, hrestL, hwf⟩ := himA
  -- (S2–S4 Probe) the buckets other than `lease` are the plain image's
  have hrest := bkRestAtL_other hrestL
  rw [← hdcm] at hkI
  imod image_restoreRes E γr d A' r D hkI hr $$ HkI HrI Hcp HA' Hrcp with ⟨#Hrcpt, #Hpf, #Hpc⟩
  imodintro
  isplitl [Hhi]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hrn Hmem HH HL HG HU]
  · iapply srvRestRp_close
    iexists f
    iframe HL HG HRq HU
    isplitr
    · ipureintro; exact Hf
    rw [hRO]
    iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hrn
    rw [apply.restLeasesWith_mem]
    iframe Hmem
    ipureintro; rw [← apply.restLeasesWith_mem f (srvIds E (appliedTable γr A).ids)]; exact Hmi
  iexists A', (kvModel γr.kv A').drop 2, r
  iframe HA'
  rw [hsplit]
  iframe Hrcpt Hpf Hpc
  ipureintro
  have hb := image_bootBucketsNL d hrest
  have hrok : mvcc.restoreLogOk ((kvModel γr.kv A').drop 2) := by
    unfold kvModel at hwf ⊢
    rw [hlog0] at hwf ⊢
    exact restoreLogOk_kvRaftOf _ _ A' Hpl hwf
  exact {
    pre := hAA'
    len := by omega
    log := hsplit
    hpre := by rw [Hl, hsplit]; exact kvRaftOf_prefix _ _ _ _ _ hAA'
    hkI := by rw [hsplit]; exact hkI
    crev := hr
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hRok := hrok
    hlen := kvModel_len_of_rok γr.kv A' _ hsplit hrok
    hlease := imageLeasesAt_of_bkRestAtL d hrestL
    halarm := hb.1
    hauthb := hb.2
    hmemb := image_membBucketsNL d hrest
    himg := clusterImageOk_of_NL d cl _ hrest Himg
    hA' := ⟨restModel_bk_of_NL d hrest, rfl⟩ }

/-- **`snapRecv_imageOn` inside the window** (DRAFT): at an image `r0` with the model's ids. -/
theorem snapRecv_imageOnR (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (sa : auth.AuthState) (_hkb : E.γ.kb = some d)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain true false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H) (hlg : E.lg = false)
    (r0 : apply.RestM)
    (hids : ∀ k, (r0.mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).mem !! k).isSome) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗ srvRestRp E γr A r0 -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRestRp E γr A r0 ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log) (r : mvcc.CmpRecs), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A' x R r
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗
        mvcc.crevPermAt E.γ r.crev := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [srvRestRp_false E γr A r0 hlg]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, %Hcok, #Hcp, -⟩
  -- the certificate's KV names agree with the member's on the start values
  iunfold srvImageOn at Himg
  icases Himg with ⟨%γk', %hk', #Hdb⟩
  obtain ⟨h0', h1', h2'⟩ := hk'
  have hR : ∀ B, kvRaftOfOn γk'.c0 γk'.ch0 (srvAuthSt0, γk'.log0) B =
      kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) B := by
    intro B; rw [h0', h1', h2', hc0, hch, hlog0]
  have hk : ∀ B, kvModelOn γk' srvAuthSt0 B = kvModelOn γr.kv srvAuthSt0 B := by
    intro B; unfold kvModelOn; rw [hR]
  have hsa : ∀ B, srvAuthAtLog γk' srvAuthSt0 B = srvAuthAtLog γr.kv srvAuthSt0 B := by
    intro B; unfold srvAuthAtLog; rw [hR]
  have hcr : ∀ B, crevOf γk' B = crevOf γr.kv B := by
    intro B; simp only [crevOf, h0', h1', hc0, hch]
  iunfold dbImageOn at Hdb
  icases Hdb with ⟨%A', #HA'0, %hA', #Hrcp0⟩
  ihave #HA' : srvRLogLb γr.raft A' $$ []
  · rw [hraft]; iexact HA'0
  obtain ⟨hlen', himA⟩ := hA'
  simp only at hlen'
  rw [hz] at hlen'
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedLOn at Hal
  icases Hal with ⟨#HA, Hhi, #Hc, %Hl⟩
  ihave %Hcmp := srvRLogLb_prefix γr.raft A A' $$ [HA HA']
  · iframe HA HA'
  rw [hai0, hz] at hai
  have hAA' : A <+: A' := by
    rcases Hcmp with h | h
    · exact h
    · have := h.length_le; omega
  imod kv_log_ccOkOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hcc
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hpl
  -- the cluster's in-memory members, from the rest resource
  rw [hRO]
  iunfold srvRestOwnH at Hrest
  icases Hrest with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hrn, Hmem, %Hmi⟩
  ihave #HA'' : srvRLogLb γr.raft (γr.raft.pre ++ A') $$ []
  · rw [hpre0, List.nil_append]; iexact HA'
  have hLL : γr.raft.pre ++ A <+: γr.raft.pre ++ A' := (List.prefix_append_right_inj _).2 hAA'
  have hbl : γr.raft.raft.boot.length ≤ (γr.raft.pre ++ A').length := by
    rw [hpre0, hrr, List.nil_append]; omega
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccBootOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_static _ _ (Hcc m hm ht)
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' _ hids $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  -- the image's clauses at the member's names
  obtain ⟨⟨r, hkI, hr⟩, hci, htm, hrest, hauth, hwf⟩ := himA
  rw [hk] at hkI hwf
  rw [hcr] at hr
  rw [hsa] at hauth
  have hrest' : bkRestAtNA γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A') D := by
    intro n hn hna
    rw [hrest n hn hna, hpre0, hrr, hc0, h0']
  have hcrev : crevOf γr.kv A' = -1 := crevOf_plainOn γr.kv A' Hpl
  have hb : mvcc.LogB (kvModelOn γr.kv srvAuthSt0 A') := ⟨by have := hwf.2.1; omega, hwf.2.2.2⟩
  have hkI' : mvcc.keyImageM d.cm (kvModelOn γr.kv srvAuthSt0 A') r D :=
    mvcc.keyImageM_mode _ _ _ r D hb hkI (fun _ _ => by rw [hr, hcrev])
  have hre : r = mvcc.CmpRecs.empty := by
    cases hdm : d.cm with
    | false =>
      rw [hdm] at hkI'
      exact ((mvcc.keyImageM_off _ _ D).1 hkI').2
    | true =>
      rw [hdm] at hkI'
      exact mvcc.CmpRecs.empty_of_crev r (mvcc.keyImageM_recsPos _ _ _ hkI') (by rw [hr, hcrev])
  have hsplit := kvModelOn_split γr.kv srvAuthSt0 A' hlog0
  have hrok : mvcc.restoreLogOk ((kvModelOn γr.kv srvAuthSt0 A').drop 2) := by
    unfold kvModelOn at hwf ⊢
    rw [hlog0] at hwf ⊢
    exact restoreLogOk_kvRaftOfOn _ _ _ A' Hpl hwf
  ihave #Hrcp : ⧖ (mvcc.logCh (kvModelOn γr.kv srvAuthSt0 A')) $$ []
  · rw [← hk]; iexact Hrcp0
  ihave #Hrcpt : mvcc.restoreRcptM (GF := GF) d (kvModelOn γr.kv srvAuthSt0 A') $$ []
  · unfold mvcc.restoreRcptM
    split
    · iexact Hrcp
    · itrivial
  imodintro
  isplitl [Hhi]
  · iunfold kvAppliedOn
    iunfold kvAppliedLOn
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hrn Hmem HH]
  · iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hrn Hmem
    ipureintro; exact Hmi
  iexists A', (kvModelOn γr.kv srvAuthSt0 A').drop 2, r
  iframe HA'
  rw [hsplit]
  iframe Hrcpt
  have hxl : x.log = kvModelOn γr.kv srvAuthSt0 A := by
    unfold kvModelOn; rw [← Hl]
  have hTnil : (appliedTable γr A').ids = [] := by
    unfold appliedTable kvLeases; rw [hpre0, List.nil_append, kvTableOf_plainOn _ _ A' Hpl]; rfl
  have hfacts : SnapImageFactsOn γr d D cl i A A' x ((kvModelOn γr.kv srvAuthSt0 A').drop 2) r
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem := {
    pre := hAA'
    len := by omega
    log := hsplit
    hpre := by rw [hsplit, hxl]; exact kvModelOn_prefix _ _ hAA'
    hkI := by rw [hsplit]; exact hkI'
    crev := hr
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hRok := hrok
    hlen := by
      rw [← hsplit]
      have := hrok.2.1.2.1
      omega
    hlease := imageLeasesAt_of_nil hTnil (image_leaseAlarmNA d hrest').1
    halarm := (image_leaseAlarmNA d hrest').2
    hauthI := authBucketsAt_rbData d D _ hauth
    hmemb := image_membBucketsNA d hrest'
    himg := clusterImageOk_of_bkRestAtNA d cl _ hrest' Himg
    hA' := ⟨restModel_bk_of_bkRestAtNA d hrest', rfl⟩ }
  isplitr
  · ipureintro; exact hfacts
  subst hre
  rw [mvcc.CmpRecs.finRev_empty, mvcc.CmpRecs.crev_empty]
  isplitr <;> iapply mvcc.crevPermAt_none

end recvR

end EtcdGrove
end Perennial
