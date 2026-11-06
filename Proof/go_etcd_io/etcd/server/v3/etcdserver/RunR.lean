/-
**The apply thread's resources in restart form and a job's body over them** (R2d' probe, step 3,
2026-11-06; DRAFT: nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved
2026-11-06)", its probe). Lean-first (no Rocq counterpart).

At the etcd pin `673da07c8`, a restarted member's scheduler runs the same jobs as a first start's
(`s.applyAll(&ep, &ap)`, `server.go:846`), the first ones over entries at or below the
backend's consistent index (`server.go:1940`, replayed v2-only). `applyResR` is `applyResC` with the
ghost rows (the applied index `g`, the KV model, the view, the rest buckets, the conf state's
history) at the ghost log `ghostOf rp A` while Go's rows (`ep.appliedi`, `loopOk`, the snapshot
state) stay at `A`; past the window it is `applyResC` (`applyResR_past`), and a first start's is
`applyResC`'s (`applyResR_first`).

* (swap batch 3, 2026-11-06) `winNoMergedSendR` and `srvSnapBagN` moved to `ApplyRDefs.lean`, and
  `applyAll.specBatchR` became `applyAll.specBatch` (the Spec file);
* `run_job_bodyR`: `run_job_body` over `applyResR`, for a batch inside, straddling or past the
  window.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthCompRows

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **The apply thread's resources at Go's log `A`, in restart form** (DRAFT): `applyResC`'s rows,
with the ghost rows at `ghostOf rp A` (the applied index `g`, the KV model, the rest buckets
`srvRestR`, `srvApRes`, the conf state's history), Go's at `A`; the backend's log `A₀` committed
(`srvRLogLb`), its entries normal or conf changes (raft's `EntryNormal`/`EntryConfChange`, the ones
`apply` replays), and through the consistent index (`ai₀ + |A₀| ≤ ciEff`, `bootstrap.go:255-273`). -/
def applyResR (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState) (g : w64),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerC K C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    epCsAt C.ρ.raft (ghostOf rp A) cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr g ∗ appliedLogAt C.γr g x.log ∗ kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A) x sa ∗
    srvRestR B.E C.γr rp A ∗ srvApRes C.s C.γr (ghostOf rp A) ∗ srvRLogLb C.ρ.raft rp.A₀ ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv B.E.s B.E.γ) ∗
    rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗
    (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗ acTok K (ciEff B.γ st.k) ∗
    srvSnapOwn C.s C.ci B.E C.γr B.γ ai ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ g ∧
      uint.Z g ≤ uint.Z (ciEff B.γ st.k) ∧
      lastTermIs A at' ∧
      uint.Z g = uint.Z C.ai₀ + (ghostOf rp A).length ∧ rp.b ≤ A.length ∧
      (∀ m ∈ rp.A₀, m.typ = W32 0 ∨ m.typ = W32 1) ∧
      uint.Z C.ai₀ + rp.A₀.length ≤ uint.Z (ciEff B.γ st.k) ∧
      uint.Z C.ai₀ + rp.A₀.length + 1 < 2 ^ 64⌝)

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Past the window, `applyResR` is `applyResC`** (the ghost log Go's, the ghost index Go's). -/
theorem applyResR_past (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel)
    (h : rp.A₀.length ≤ A.length) : applyResR K C rp A ⊢ applyResC K C A := by
  unfold applyResR applyResC
  simp only [ghostOf_past rp A h, srvRestR_past _ _ rp A h]
  iintro ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss, Hst,
    Hbe, Happ, Hlr, Hbr, Hwr, HKV, Hao, Hlog, Hkr, HRS, HAR, -, HKVf, Hwal, Hw, HtokR, Hso,
    %Hpure⟩
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt, Hg0, -, -, -, -⟩ := Hpure
  have hga : g = ai := by word
  subst hga
  iexists B, st, g, at', a, t, cs, x, sa
  iframe Hsrv Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hbr Hwr HKV Hao Hlog Hkr HRS HAR HKVf Hwal Hw
  iframe HtokR Hso
  ipureintro
  exact ⟨HB, Hloop, Hai0, HJ, Hci, Hlt⟩

/-- **A first start's `applyResR` is `applyResC`'s** (nothing in the window), given the empty
log's bound (`srvRLogLb _ []`) and room past the start index. -/
theorem applyResR_first (K : AuthC) (C : ApplyCtx GF) (A : List EntryModel)
    (hb : uint.Z C.ai₀ + 1 < 2 ^ 64) :
    applyResC K C A ∗ srvRLogLb C.ρ.raft [] ⊢ applyResR K C RestartPt.first A := by
  unfold applyResR applyResC
  simp only [ghostOf_first, srvRestR_first]
  simp only [RestartPt.first]
  iintro ⟨⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss, Hst,
    Hbe, Happ, Hlr, Hbr, Hwr, HKV, Hao, Hlog, Hkr, HRS, HAR, HKVf, Hwal, Hw, HtokR, Hso,
    %Hpure⟩, #Hlb⟩
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt⟩ := Hpure
  iexists B, st, ai, at', a, t, cs, x, sa, ai
  iframe Hsrv Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hbr Hwr HKV Hao Hlog Hkr HRS HAR HKVf Hwal Hw
  iframe HtokR Hso Hlb
  ipureintro
  refine ⟨HB, Hloop, Hai0, HJ, Hci, Hlt, by simpa using Hai0, Nat.zero_le _, by simp, ?_, by simpa using hb⟩
  simp only [List.length_nil]; push_cast; omega

end laws

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A job's body in restart form** (R2d' probe, DRAFT): `run_job_body` over `applyResR`, for a
batch `ce` inside, straddling or past the window (`s.applyAll(&ep, &ap)`, `server.go:846` at
`673da07c8`), from `applyAll.specBatch` (the restart form since swap batch 3). Its new premises: the notifier's payload at
the ghost log, and the window's `winNoMergedSendR` for the window left after the batch. -/
theorem run_job_bodyR (hAA : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (rp : RestartPt) (A ce : List EntryModel)
    (K : AuthC) (hM : C.E.authMode = K.mode) (hRB : acReceiptOk (GF := GF) K)
    (apL : Loc) (es : GoSlice) (ceL : List Loc) (rac nc : GoChan) (γs : schedule.SchedNames)
    (dv : Option Loc) (γnc : NotifyNames)
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : logShapeM K.isOn C.ρ.kv.lm (A ++ ce))
    (hw : C.γw = C.ρ.wait)
    -- (D43 M3, 2026-10-25) the driver's view, `applyAll`'s (`dvOk`): without one, no conf entry;
    -- with one, a fresh start (`c₀ ≤ ai₀`) at the server's rule (2026-10-30, the repair: one mode)
    (hdvn : dv = none → ∀ m, m ∈ ce → m.typ ≠ W32 1)
    (hdvs : ∀ γn, dv = some γn → uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧
      C.ρ.raft.raft.rule = srvRule C.γr.kv.c0 C.ρ.raft.raft.boot ∧ C.ρ.raft.pre = [] ∧
      C.ρ.raft.ai0 = W64 0)
    -- (2026-10-30, the repair) the node's id, whose applied index `raftAdvancedC`'s close reports
    (nk : GName)
    -- (2026-10-31, #11's S3) a fresh start (`isServerRun`'s)
    (ha00 : uint.nat C.ai₀ = 0)
    -- (2026-10-31, #11) the disk cooperating (`isServerRun`'s), for the snapshot
    (hdisk : storage.diskOk)
    -- (2026-10-31, S1: `applyAll`'s merged snapshot) the batch's raft term, good for its log
    -- (`rnApplyTok_recv`'s `rnRtOk`), at the raft node `γn` of the server's raft; the start's
    -- consistent index at most its applied one (`isServerRun`'s)
    (γn : RNNames) (rt : w64) (hγn : γn.node = C.γr.raft.raft) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀)
    -- (2026-11-03, R2b-1 stage 5) a fresh start's log, the context's raft names `γn` (the WAL's)
    (hpre : C.γr.raft.pre = []) (hrn : C.rn = γn) (T : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        acLessor K C.s ∗ isServerApplyAll C.s C.γr ∗ batchWaitOk C.ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
          iprop(nodeAppliedLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗ nodeCommitLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗
            srvFrozenRange C.γs (uint.nat C.ai₀ + A.length + 1)
              (uint.nat C.ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms C.γs (uint.nat C.ai₀ + 1) (A ++ ce) ∗
            rnWalHanded γn (uint.nat C.ai₀ + (A ++ ce).length))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗
        isNotify γnc nc (dvView C.ρ.raft dv (ghostOf rp (A ++ ce))) ∗ notifyRcv γnc ∗
        dvView C.ρ.raft dv (ghostOf rp A) ∗ dvRes C.s C.ρ.raft dv (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyResR K C rp A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft (A ++ ce) ∗
        srvSnapDisk C.s C.γr ∗
        (letI : MemStorReg GF := ⟨C.γr.raft.raft.reg⟩; memStorInv C.ms C.γs C.γr.raft.raft.cl nk) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn (A ++ ce)).length ∗
        winNoMergedSendR C.γr.raft.raft C.s γn.t0 T (rp.A₀.drop (A ++ ce).length) rt ∗ T ∗
        srvSnapBagN C.s γn }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ T ∗ applyResR K C rp (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) }} := by
  have hR : ∀ dv : Option Loc, (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) =
      srvRunH (GF := GF) C.ρ.raft dv := fun dv => by cases dv <;> rfl
  simp only [EtcdServer.applyAll.specBatch] at hAA
  rw [hR]
  iintro %Φ ⟨#Hpkg, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, Hdv, #Hdvr, Hrh, #Hesl,
    #Hents, #Hbc, Hrun, HR, #HWc, #Hlbr, #Hsd, #Hmsinv, #Hrtf, #Hrtok, #Hwnm, HT, #Hbagn⟩ HΦ
  iunfold applyResR at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HlbA0, #HKVf, Hwal, ⟨%w, #HWA⟩, HtokR, Hso, %Hpure⟩
  ihave Hwal : rnWalTokA γn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [← hrn]; iexact Hwal
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt, Hg0, Hb, Hty, HA0b⟩ := Hpure
  have hgl := ghostOf_length rp A
  -- (S1) the consistent index at most the applied one (a fresh start's at most its applied index)
  have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z g := by
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]; omega
    · exact h2
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt, Htok⟩
  have habove := srvIdxOk_batch_above C.ai₀ ai A ce hidx Hai0
  have hun : unapplied ai ce = ce := unapplied_all ai ce habove
  have hcong : ∀ m ∈ ce, uint.Z C.ai₀ + rp.A₀.length < uint.Z m.index →
      (uint.Z (ciEff B.γ st.k) < uint.Z m.index ↔ uint.Z C.c₀ < uint.Z m.index) :=
    fun m hm h => ciJ_iff _ _ _ HJ m (by have := habove m hm; omega)
  ihave %Hlgt := isServerC_lm K C.s B.γ C.ci B.TM B.E C.ρ C.γr $$ Hsrv
  have hok' : logShapeM K.isOn B.E.lm (unapplied ai ce) := by
    rw [hun]
    cases hK : K.isOn
    · rw [hK, logShapeM_false] at hok
      rw [logShapeM_false, ← Hlgt.2 hK, ← Hlgt.1]
      exact ((logShape_append _ A ce).1 hok).2
    · rw [hK] at hok
      exact fun m hm => hok m (List.mem_append_right A hm)
  have hb1 : uint.Z ai + 1 < 2 ^ 64 := by
    have h1 := hidx.1
    simp only [List.length_append] at h1
    push_cast at h1
    have : (0 : Int) ≤ ce.length := by omega
    omega
  -- (D43 M3) the view's premise: a fresh start's consistent index is at most the applied one
  have hdv : dvOk C.ρ.raft C.γr.kv.c0 dv (ciEff B.γ st.k) (g + 1) (unapplied ai ce) := by
    rw [hun]
    refine ⟨hdvn, fun γn h => ⟨?_, (hdvs γn h).2⟩⟩
    have hg1 : uint.Z (g + 1) = uint.Z g + 1 := by
      have := hidx.1; simp only [List.length_append] at this; push_cast at this; word
    rw [hg1]
    omega
  have hms : ce = [] ∨ (entriesFrom (ai + 1) ce ∧ uint.Z (ai + 1) ≤ uint.Z ai + 1) := by
    by_cases hne : ce = []
    · left; exact hne
    · right
      obtain ⟨h1, h2⟩ := srvIdxOk_batch_from C.ai₀ ai A ce hidx Hai0 hne
      exact ⟨h1, by omega⟩
  ihave #Hbw' : iprop(batchWaitOk C.ρ B.E ce) $$ []
  · rw [batchWaitOk_beSucc HB]
    iunfold batchWaitOk at Hbw
    iunfold batchWaitOk
    imodintro
    iintro %m %hm
    iapply Hbw
    ipureintro; exact List.mem_append_right A hm
  have Hρr := Hlgt.1
  ihave Hkr : iprop(kvAppliedM K.isOn C.γr.raft C.γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗
      ⌜C.γr.kv.c0 = C.c₀ ∧ C.γr.raft.ai0 = C.ai₀⌝) $$ [Hkr]
  · rw [← kvRunM_split]; iexact Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  ihave #Hkb : iprop(kvBatchR C.γr (ciEff B.γ st.k) ai rp A ce) $$ []
  · iunfold kvBatchR
    isplitr
    · rw [← Hρr]; iexact Hlbr
    isplitr
    · rw [← Hρr]; iexact HlbA0
    ipureintro
    refine ⟨by rw [Hkc.2]; exact Hai0, Hb, by rw [Hkc.2]; omega, by rw [Hkc.1, Hkc.2]; exact hc0, Hty,
      fun m hm h => ?_⟩
    rw [Hkc.1]; rw [Hkc.2] at h; exact hcong m hm h
  -- (D19i part 1) the floor past the batch, at its last index (`srvIdxOk_batch_last`)
  have e1 : (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat =
      uint.nat C.ai₀ + (A ++ ce).length := by
    rw [srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0]; word
  have e2 : uint.nat ai + 1 = uint.nat C.ai₀ + A.length + 1 := by word
  ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
      iprop(nodeAppliedLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ nodeCommitLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
        srvFrozenRange C.γs (uint.nat ai + 1)
          ((max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
        srvFrozenTerms C.γs 1 (A ++ ce) ∗
        rnWalHanded γn (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat))
      $$ []
  · rw [e1, e2]; iExactEq Hracc; rw [ha00]
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  iapply (hAA C.s B.γ C.ci B.TM K B.E C.ρ C.γr B.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x sa A
      C.ms C.γs C.wt dv γnc w nk (1 : Qp).half γn rt (rnLogOf γn (A ++ ce)).length rp g T)
    $$ [Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS Hnrc Hdv HAR HtokR Hrh Hwal Hso HT]
  · isplitr
    · iexact Hpkg
    isplitr
    · ipureintro
      exact ⟨by rw [beSucc_authMode HB]; exact hM, hRB, hms, hb1, Hloop, hok', hdv,
        by have := uint_nat_eq C.ai₀; omega, Hlt, hdisk, Hci, hcia, by rw [Hkc.2]; exact Hg0, hγn, hpre,
        by rw [hun]; simp [rnLogOf]⟩
    rw [hun]
    iframe Hwnm HT Hbagn
    iframe Hsd Hmsinv HKVf Hwal Hrtf Hrtok
    iframe HWc' Hracc' Hcv Hkb Hbw' HWA Hlog Hsrv Hlnil Hbc Hents Hesl Hncb Hnc Hsn Hrac Hes Hsa
    iframe
    iunfold srvGoRes
    iframe
    isplitl [Hdvr]
    · iexact Hdvr
    iExactEq Hrh; cases dv <;> rfl
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %g', %HB', HT, Hrh, #Hsrv', -, HAR, Hai, Hat, Hcs, #Hcv', Hss, Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, #HWA', ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, #HKVf', Hwal, Hso, %Hpost⟩
  ihave Hwal : rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [hrn]; iexact Hwal
  obtain ⟨hg', hloop', hai', hci', hciN, hat'⟩ := Hpost
  rw [hun, Hkc.2] at hg'
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok HT
  isplitr [Hrh]
  rotate_left
  · iExactEq Hrh; cases dv <;> rfl
  ihave Hkr : iprop(kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp (A ++ ce)) x' sa') $$ [Hka]
  · rw [kvRunM_split]
    isplitl [Hka]
    · iapply (show kvAppliedM (GF := GF) K.isOn C.γr.raft C.γr.kv srvAuthSt0
          (ghostOf rp (A ++ unapplied ai ce)) x' sa' ⊢
        kvAppliedM K.isOn C.γr.raft C.γr.kv srvAuthSt0 (ghostOf rp (A ++ ce)) x' sa' from by rw [hun]) $$ Hka
    ipureintro; exact Hkc
  ihave HRS : iprop(srvRestR E' C.γr rp (A ++ ce)) $$ [HRS]
  · iapply (show srvRestR (GF := GF) E' C.γr rp (A ++ unapplied ai ce) ⊢ srvRestR E' C.γr rp (A ++ ce)
      from by rw [hun]) $$ HRS
  ihave HAR : iprop(srvApRes C.s C.γr (ghostOf rp (A ++ ce))) $$ [HAR]
  · iapply (show srvApRes (GF := GF) C.s C.γr (ghostOf rp (A ++ unapplied ai ce)) ⊢
      srvApRes C.s C.γr (ghostOf rp (A ++ ce))
      from by rw [hun]) $$ HAR
  ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
  · rw [← beSucc_γbe HB]; iexact Hbr
  iunfold applyResR
  rw [hw]
  iexists ⟨γ', TM', E', b'⟩, st', ai', at'', a', t', cs', x', sa', g'
  isplitr
  · ipureintro; exact beSucc_trans HB HB'
  iframe Hsrv'
  ihave #Hcv'' : epCsAt C.ρ.raft (ghostOf rp (A ++ ce)) cs' $$ []
  · rw [show A ++ ce = A ++ unapplied ai ce by rw [hun]]; iexact Hcv'
  iframe Hcv'' HKVf' HlbA0
  iframe
  iframe Hlog'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  isplitr
  · iexists w + (unapplied ai ce).length
    iexact HWA'
  ipureintro
  rw [hun] at Hx'
  have hgl' := ghostOf_length rp (A ++ ce)
  have hlc : (A ++ ce).length = A.length + ce.length := List.length_append
  have hgg : uint.Z g ≤ uint.Z g' := by rw [Hg0, hg', hgl, hgl', hlc]; omega
  have hcN := hciN Hci
  have e1 : uint.Z ai' = uint.Z C.ai₀ + (A.length + ce.length : Nat) := by
    rw [hai', hlast, hlc]
  have e2 : uint.Z g' = uint.Z C.ai₀ +
      (A.length + ce.length + (rp.A₀.length - (A.length + ce.length)) : Nat) := by
    rw [hg', hgl', hlc]
  have hA0' : uint.Z C.ai₀ + rp.A₀.length ≤ uint.Z (ciEff γ' st'.k) := by
    have := HA0b.1
    rcases hci' with h | h
    · rw [h]; exact this
    · omega
  refine ⟨hloop', by rw [hai', hlast], ?_, hcN, ?_, hg', by rw [hlc]; omega, Hty, hA0', HA0b.2⟩
  · apply ciJ_step _ _ _ g g' HJ hgg
    rcases hci' with h | h
    · exact Or.inl h
    · right
      have := HA0b.1
      rw [h, e1, e2]
      omega
  · rw [hun] at hat'; exact lastTermIs_append Hlt hat'

end proof

end EtcdGrove
end Perennial
