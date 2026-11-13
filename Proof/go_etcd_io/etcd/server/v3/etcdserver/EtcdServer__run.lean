/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__run.lean`. Lean-first (no Rocq
counterpart); see `InvRun.lean`.

Since R2d'a swap batch 5 (2026-11-07) the proof is the restart's (`isServerRunC`'s `srvRunRestartR`;
restart S4, 2026-11-12, at any WAL snapshot index: Go's start log `P`, the backend's ghost log
`A₀ = γn.a0` replayed through the window `(|P|, |A₀|]`; a first start is `A₀ = P = []`), `notes/restart-plan.md`, "Swap batch 5". The pieces, from the drafts this batch deleted
(`ViewR`, `RunR`, `RunSnapR`, `StartR`, `StopR`, `RunRestart`):
* `rnApR_dv`/`rnApGive_dv`: the driver's view over the ghost log, as the apply side states it;
* `applyResR`: the loop's resources in restart form; `run_job_body`, a batch job over it;
* `run_job_snapC`: a snapshot-payload job over it;
* `applyResR_start`: the loop's resources at the start, from `srvRunRestartR`'s `srvRestartAtR`;
* `stop_split`: what `raftNode.stop` takes of them;
* `run.wp_proofG`, `run.wp_proof`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__BecomeLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopShutdown
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver


section view
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ### The driver's view, as the apply side states it (R2d'a A10; swap batch 5, 2026-11-07, from
`ViewR.lean`'s `rnApR_dvG`/`rnApGive_dvG`, which replaced `InvRaftLoop.lean`'s first-start forms)

Since A6 the raft loop's view is over the ghost log (`rnView γ L`, the view after `rnGhost γ L`, which
is `ghostOf ⟨b, γ.a0⟩ (γ.pre ++ L)` for any `b`); the apply side's `pre` is `[]` and its log Go's,
`γ.pre ++ F` (no `γ.pre = γs.pre`, which a restart breaks). -/

/-- **What the apply thread's `notifyc` receive deposits, as the apply side states it**: the view
after the batch over the ghost log, if it went along (no `γ.a0 = []`). -/
theorem rnApR_dv (γ : RNNames) (γs : ServerRaftNames) (b : Nat) (hpre : γs.pre = [])
    (hraft : γs.raft = γ.node) (F ce : List EntryModel) :
    rnApR (GF := GF) γ F ce = dvView γs (rnDv γ ce) (ghostOf ⟨b, γ.a0⟩ (γ.pre ++ F ++ ce)) := by
  have hv : ∀ L, rnView (GF := GF) γ L =
      srvCfgView γ.srv γ.nl [] (ghostOf ⟨b, γ.a0⟩ (γ.pre ++ L)) := fun _ => rfl
  unfold rnApR rnDv dvView
  by_cases h : rnHands γ ce
  · rw [ite_eq_left h, ite_eq_left h, hv]
    unfold srvCfgView
    rw [hraft, hpre, List.append_assoc]
  · rw [ite_eq_right h, ite_eq_right h]

/-- **What goes along with a batch, as the apply side states it** (with the node's conf-change
contract, `isRaftNodeIfc`'s): the view over the ghost log of Go's log before the batch, the
delivered log over Go's log through it (no `γ.a0 = []`). -/
theorem rnApGive_dv (s : Loc) (γ : RNNames) (γs : ServerRaftNames) (b : Nat)
    (hpre : γs.pre = []) (hraft : γs.raft = γ.node) (F ce : List EntryModel) :
    srvRaftNodeCC (GF := GF) s γ.srv γ.nl ∗ rnApGive γ F ce ⊢
      dvView γs (rnDv γ ce) (ghostOf ⟨b, γ.a0⟩ (γ.pre ++ F)) ∗
        dvRes s γs (rnDv γ ce) (γ.pre ++ F ++ ce) := by
  have hv : ∀ L, rnView (GF := GF) γ L =
      srvCfgView γ.srv γ.nl [] (ghostOf ⟨b, γ.a0⟩ (γ.pre ++ L)) := fun _ => rfl
  unfold rnApGive rnDv dvView dvRes
  by_cases h : rnHands γ ce
  · rw [ite_eq_left h, ite_eq_left h]
    simp only
    rw [hv, srvRaftNodeCC_congr s γs γ.srv γ.nl hraft]
    unfold srvCfgView srvLE
    rw [hraft, hpre]
    simp only [RNNames.srv, List.nil_append, List.append_assoc]
    iintro ⟨#Hn, Hv, #Hd⟩
    iframe Hv Hn Hd
  · rw [ite_eq_right h, ite_eq_right h]
    simp only
    iintro -
    isplitr
    · ipureintro; trivial
    ipureintro; trivial

end view


section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- **The apply thread's resources at Go's log `A`, in restart form** (`run`'s loop invariant and its
jobs' `Prev`/`Post`; from `RunR.lean`, swap batch 5): the first-start `applyResC`'s rows
(`applyResC` deleted 2026-11-07), with the ghost rows at `ghostOf rp A` (the applied index `g`, the KV model, the rest buckets
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
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ mvcc.api.mvccReaders B.E.γ 1 ∗
    srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr g ∗ appliedLogAt C.γr g x.log ∗ kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A) x sa ∗
    srvRestR B.E C.γr rp A ∗ srvApRes C.s C.γr (ghostOf rp A) ∗ srvRLogLb C.ρ.raft rp.A₀ ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ □ mvcc.api.isMvcc kv B.E.γ ∗ ⌜kv = B.E.kv⌝) ∗
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A job's body in restart form** (R2d' probe; swap batch 5: `RunR.lean`'s `run_job_bodyR`, in
place of the first-start `run_job_body` over `applyResC`): over `applyResR`, for a
batch `ce` inside, straddling or past the window (`s.applyAll(&ep, &ap)`, `server.go:846` at
`673da07c8`), from `applyAll.specBatch` (the restart form since swap batch 3). Its new premises: the notifier's payload at
the ghost log, and the window's `winNoMergedSendR` for the window left after the batch. -/
theorem run_job_body (hAA : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (rp : RestartPt) (A ce : List EntryModel)
    (K : AuthC) (hM : C.E.authMode = K.mode) (hRB : receiptBound GF ≤ 2 ^ 48)
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
    -- (2026-10-31, #11's S3) a fresh start (`isServerRunC`'s)
    (ha00 : uint.nat C.ai₀ = 0)
    -- (2026-10-31, #11) the disk cooperating (`isServerRunC`'s), for the snapshot
    (hdisk : storage.diskOk)
    -- (2026-10-31, S1: `applyAll`'s merged snapshot) the batch's raft term, good for its log
    -- (`rnApplyTok_recv`'s `rnRtOk`), at the raft node `γn` of the server's raft; the start's
    -- consistent index at most its applied one (`isServerRunC`'s)
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
    Hwr, Hrdk, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HlbA0, #HKVf, Hwal, ⟨%w, #HWA⟩, HtokR, Hso, %Hpure⟩
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
    $$ [Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hwr Htok Hrdk Hbr HKV Hao Hka HRS Hnrc Hdv HAR HtokR Hrh Hwal Hso HT]
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
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %g', %HB', HT, Hrh, #Hsrv', -, HAR, Hai, Hat, Hcs, #Hcv', Hss, Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, Hao,
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

section jobs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `run_job_body`'s running half, as `srvRunH` (`SDRun.lean`). -/
theorem run_job_body_match (γs : ServerRaftNames) (dv : Option Loc) :
    run_job_body.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning (GF := GF) n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH (GF := GF) γs dv := by
  cases dv <;> rfl

/-- **The apply side's half of the running token, lent to a job** (2026-10-30, the repair): the
job's view `rnDv γn ce` is the node's or none; with the node's, the half is `srvRunH`'s. -/
theorem srvRunH_lend (γn : RNNames) (γs : ServerRaftNames) (hnd : γs.raft = γn.node)
    (ce : List EntryModel) :
    (letI := srvStor (GF := GF) γn.node; nodeRunning (GF := GF) γn.nl γn.node.cl srvClusterN (1 : Qp).half) ⊢
      srvRunH (GF := GF) γs (rnDv γn ce) ∗
        (srvRunH (GF := GF) γs (rnDv γn ce) -∗
          (letI := srvStor (GF := GF) γn.node; nodeRunning (GF := GF) γn.nl γn.node.cl srvClusterN (1 : Qp).half)) := by
  unfold rnDv
  split
  · rw [srvRunH_some, hnd]
    iintro H
    iframe H
    iintro H; iexact H
  · rw [srvRunH_none]
    iintro H
    isplitr
    · itrivial
    iintro -; iexact H

end jobs


section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest buckets at an image of the ghost log**: inside the window (Go's log a prefix
of the backend's) the replay's image of `A₀`, past it the model of Go's log; either way its members
have the model's ids. -/
theorem srvRestR_img (E : apply.AEnv GF) (γr : ReadNames) (rp : RestartPt) (A : List EntryModel)
    (h : A <+: rp.A₀ ∨ rp.A₀ <+: A) :
    ∃ r0 : apply.RestM, (∀ k, (r0.mem !! k).isSome =
        ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ ghostOf rp A)).mem !! k).isSome) ∧
      srvRestR E γr rp A = srvRestRp E γr (ghostOf rp A) r0 := by
  by_cases hl : A.length < rp.A₀.length
  · have hp : A <+: rp.A₀ := h.resolve_right (fun h' => by have := h'.length_le; omega)
    refine ⟨restReplay γr rp A, ?_, ?_⟩
    · intro k; rw [ghostOf_in rp A hp]; exact restReplay_memKeys γr rp A k
    · rw [srvRestR_in E γr rp A hl, ghostOf_in rp A hp]
  · have hp : rp.A₀.length ≤ A.length := by omega
    refine ⟨restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ ghostOf rp A), fun _ => rfl, ?_⟩
    rw [srvRestR_past E γr rp A hp, ghostOf_past rp A hp, srvRestRp_model]

/-- **The start chain's auth layer is the component's** (`kvInv_ch0_off`/`kvInvOn_ch0` over the
server's view). -/
theorem isServerC_ch0 (K : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerC K s γ ci TM E ρ γr ⊢ |={⊤}=> ⌜γr.kv.ch0 = apply.alarmChain K.isOn false false⌝ := by
  iintro #H
  ihave #H' := (isServerM_C K s γ ci TM E ρ γr).2 $$ H
  iunfold isServerM at H'
  icases H' with ⟨-, -, -, #Hatm, -, -⟩
  iunfold srvAtomicsM at Hatm
  icases Hatm with ⟨-, -, #Hki⟩
  cases K with
  | off =>
    ihave #Hki := (show srvKVInvsM (GF := GF) AuthC.off.isOn s E γr ⊢ srvKVInvs E γr from .rfl) $$ Hki
    iunfold srvKVInvs at Hki
    icases Hki with ⟨#Hkv, -⟩
    imod (kvInv_ch0_off γr.raft γr.kv) $$ Hkv with %h
    imodintro; ipureintro; exact h
  | on γa =>
    ihave #Hki := (show srvKVInvsM (GF := GF) (AuthC.on γa).isOn s E γr ⊢ srvKVInvsOn E γr srvAuthSt0
      from srvKVInvsM_true s E γr) $$ Hki
    iunfold srvKVInvsOn at Hki
    icases Hki with ⟨#Hkv, -⟩
    imod (kvInvOn_ch0 γr.raft γr.kv srvAuthSt0) $$ Hkv with %h
    imodintro; ipureintro; exact h

end laws

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 1000000 in
/-- **`run`'s snapshot-payload job in restart form** (R2d'a task 4; swap batch 5: `RunSnapR.lean`'s
`run_job_snapCR`, in place of the first-start `run_job_snapC`, `run_job_snap` off and `run_snap_jobOn`
on, over `applyAll.specSnap`): over `applyResR` and `applyAll.specSnapM`, inside the window or past it; Go's handed log committed
(`srvRLogLb … A`, the loop's) places it against the backend's log, and the snapshot is above the
ghost log (`hwin`). After, Go is past the window (`applyResR … A'`). -/
theorem run_job_snapC (hAA : EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (rp : RestartPt) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64) (K : AuthC) (hM : C.E.authMode = K.mode)
    (ha00 : uint.nat C.ai₀ = 0) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hpre : γn.pre = [])
    (hγn : γn.node = C.γr.raft.raft) (hρ : C.ρ.raft = C.γr.raft)
    (hpr : C.γr.raft.pre = γn.pre) (hγs : C.γs = γn.γs) (hγw : C.γw = C.ρ.wait)
    -- (R2d'a task 4) the snapshot above the ghost log (inside the window, A8's bound)
    (hwin : (ghostOf rp A).length < A'.length)
    (hlen : (γn.pre ++ A').length = uint.nat sv.Metadata'.Index')
    (h61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (hboot : (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index') (hrn : C.rn = γn) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗
        isNotify2 γnc nc (walBaseLb γn.wal.loc (uint.nat sv.Metadata'.Index')) iprop(True) ∗
        notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length ∗
            rnWalHanded γn (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyResR K C rp A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' ∗
        srvRLogLb C.ρ.raft A }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyResR K C rp A' }} := by
  iintro %Φ ⟨#Hpkg, #Hsa, #Hmid, #Hmeta, #Hes, #Hesl, #Hsnf, Hsnv, #Hcl, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #Hrtok, Hrun, HR, #HWc, #Hlbr, #HlbA⟩ HΦ
  iunfold applyResR at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss,
    Hst, Hbe, Happ, Hlr, Hbr, Hwr, Hrdk, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HlbA0, #HKVf, Hwal, ⟨%w, #HWA⟩,
    HtokR, Hso, %Hpure⟩
  ihave Hwal : rnWalTokA γn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [← hrn]; iexact Hwal
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt, Hg0, Hb, Hty, HA0b⟩ := Hpure
  ihave Hkr : iprop(kvAppliedM K.isOn C.γr.raft C.γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗
      ⌜C.γr.kv.c0 = C.c₀ ∧ C.γr.raft.ai0 = C.ai₀⌝) $$ [Hkr]
  · rw [← kvRunM_split]; iexact Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt0, Htok⟩
  -- the fresh start's facts
  have hai0 : C.ai₀ = W64 0 := by have := uint_nat_eq C.ai₀; word
  have hpre' : C.γr.raft.pre = [] := by rw [hpr]; exact hpre
  have hiA : (uint.nat sv.Metadata'.Index' : Int) = A'.length := by rw [← hlen, hpre]; simp
  have hiZ := uint_nat_eq sv.Metadata'.Index'
  have hz0 : uint.Z (W64 0) = 0 := by word
  have hgl := ghostOf_length rp A
  have hAL : uint.Z g = (ghostOf rp A).length := by rw [Hg0, hai0, hz0]; simp
  have hag : uint.Z ai ≤ uint.Z g := by rw [Hai0, Hg0, hgl]; push_cast; omega
  have hgi : uint.Z g < uint.Z sv.Metadata'.Index' := by
    have : ((ghostOf rp A).length : Int) < A'.length := by exact_mod_cast hwin
    omega
  have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z g := by
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]; rw [hai0] at hc0; omega
    · exact h2
  have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0; word
  have hraft : C.γr.raft = ⟨C.γr.raft.raft, [], W64 0⟩ := by
    have h1 := Hkc.2
    rw [hai0] at h1
    cases hr : C.γr.raft
    simp only [hr] at hpre' h1
    simp [hpre', h1]
  -- the mode: the current backend's the component's
  have hMB : B.E.authMode = K.mode := (beSucc_authMode HB).trans hM
  have hon : B.E.authOn = K.isOn := by
    simp only [apply.AEnv.authOn, hMB, AuthC.mode_isOn]
  have hany : B.E.authMode ≠ .any := by rw [hMB]; cases K <;> simp [AuthC.mode]
  imod isServerC_ch0 K C.s B.γ C.ci B.TM B.E C.ρ C.γr $$ Hsrv with %hch
  -- (R2d'a task 4) the rest buckets at an image of the ghost log with the model's ids
  ihave %HpA := srvRLogLb_prefix C.γr.raft A rp.A₀ $$ [HlbA HlbA0]
  · rw [← hρ]; iframe HlbA HlbA0
  obtain ⟨r0, hids, hRS⟩ := srvRestR_img B.E C.γr rp A HpA
  ihave HRS : srvRestRp B.E C.γr (ghostOf rp A) r0 $$ [HRS]
  · rw [← hRS]; iexact HRS
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
  have hn : uint.nat sv.Metadata'.Index' ≤ (rnLogOf γn A').length := by
    simp only [rnLogOf, List.length_map]; omega
  -- the job's resources at the current backend `B`
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  ihave #Hmeta' : srvMetaSnap B.γ $$ []
  · have hms : srvMetaSnap (GF := GF) B.γ = srvMetaSnap C.γ := by
      rw [HB.1]; exact srvMetaSnap_withPh _ _
    rw [hms]; iexact Hmeta
  iunfold srvMetaSnap at Hmeta'
  ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
      iprop(nodeAppliedLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
        nodeCommitLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
        srvFrozenAt C.γs (uint.nat sv.Metadata'.Index') ∗
        srvFrozenBelow C.γs (uint.nat sv.Metadata'.Index') ∗
        rnWalHanded γn (uint.nat sv.Metadata'.Index'))) $$ []
  · rw [hρ, ← hγn, hγs, ← hlen]; iexact Hracc
  ihave #Hcl' : (letI := srvStor (GF := GF) C.γr.raft.raft; iprop(
      snapshotCert C.γr.raft.raft.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
      nodeSnapLocal C.γr.raft.raft.cl γn.id sv.Metadata'.Index')) $$ []
  · rw [← hγn]; iexact Hcl
  ihave #HsrvM : isServerM K.isOn C.s B.γ C.ci B.TM B.E C.ρ C.γr $$ []
  · iapply (isServerM_C K C.s B.γ C.ci B.TM B.E C.ρ C.γr).2 $$ Hsrv
  ihave HKV : srvApplyKVM K.isOn C.s B.E C.ρ.wait x sa $$ [HKV]
  · rw [← hγw]; iapply (srvApplyKVM_C K C.s B.E C.γw x sa).2 $$ HKV
  have hS := hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es sn sv rac nc st ai at' a t cs x
    (ghostOf rp A) C.ms C.γs C.wt γnc w γn.id γn.key (1 : Qp).half γn rt (rnLogOf γn A').length sa
    g r0 hany hag hgi h61 (by rw [← hγn]; exact hboot) hAL hcia hids hraft (by rw [Hkc.1, hc00])
    (by rw [hon]; exact hch) Hlog0 hγn hn
  rw [hon] at hS
  iapply hS
    $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hrdk Hbr HKV Hao Hka HRS HAR Hwal Hso Hsnv Hnr0]
  · iframe #
    iframe
    iunfold srvGoRes
    iframe
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %A'', %cs', %HB', #Hsrv'', HAR, #Hlb'', Hai, Hat, Hcs,
    #Hcv', Hss, Hst, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, Hao, #Hal, #HWA', ⟨%x', HKV, #Hlog', Hka, HRS⟩,
    #HKVf', Hwal, Hso, %Hpost⟩
  ihave Hwal : rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [hrn]; iexact Hwal
  obtain ⟨hloop', hci', -, hlen'', hlast⟩ := Hpost
  -- the image's log is raft's `A'`: both committed, of the snapshot's length
  ihave #Hlbr' : srvRLogLb C.γr.raft A' $$ []
  · rw [← hρ]; iexact Hlbr
  ihave %Hpf := srvRLogLb_prefix C.γr.raft A'' A' $$ [Hlb'' Hlbr']
  · iframe Hlb'' Hlbr'
  have hA : A'' = A' := by
    have h1 : A''.length = A'.length := by
      rw [hpre'] at hlen''; simp only [List.nil_append] at hlen''; omega
    rcases Hpf with h | h
    · exact h.eq_of_length h1
    · exact (h.eq_of_length h1.symm).symm
  subst hA
  -- Go past the window: the ghost log Go's
  have hpast : rp.A₀.length ≤ A''.length := by
    have := ghostOf_length rp A; omega
  have hgA : ghostOf rp A'' = A'' := ghostOf_past rp A'' hpast
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  have hMB' : E'.authMode = K.mode := (beSucc_authMode HB').trans hMB
  have hon' : E'.authOn = K.isOn := by
    simp only [apply.AEnv.authOn, hMB', AuthC.mode_isOn]
  ihave #Hsrv3 : isServerC K C.s γ' C.ci TM' E' C.ρ C.γr $$ []
  · iapply (isServerM_C K C.s γ' C.ci TM' E' C.ρ C.γr).1; rw [← hon]; iexact Hsrv''
  ihave HKV : srvApplyKVC K C.s E' C.γw x' (srvAuthAtLog C.γr.kv srvAuthSt0 A'') $$ [HKV]
  · iapply (srvApplyKVM_C K C.s E' C.γw x' _).1; rw [hγw, ← hon]; iexact HKV
  ihave Hkr : kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A'') x' (srvAuthAtLog C.γr.kv srvAuthSt0 A'')
    $$ [Hka]
  · rw [kvRunM_split, hgA, ← hon]
    iframe Hka
    ipureintro; exact Hkc
  ihave HRS : srvRestR E' C.γr rp A'' $$ [HRS]
  · rw [srvRestR_past E' C.γr rp A'' hpast]; iexact HRS
  ihave HAR : srvApRes C.s C.γr (ghostOf rp A'') $$ [HAR]
  · rw [hgA]; iexact HAR
  ihave #Hcv'' : epCsAt C.ρ.raft (ghostOf rp A'') cs' $$ []
  · rw [hgA]; iexact Hcv'
  -- the token rights at the snapshot's consistent index
  ihave HtokR := acTok_mono K _ sv.Metadata'.Index' (by omega) $$ HtokR
  ihave HtokR : acTok K (ciEff γ' st'.k) $$ [HtokR]
  · rw [hci']; iexact HtokR
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt0 Htok
  ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
  · rw [← beSucc_γbe HB]; iexact Hbr
  iunfold applyResR
  iexists ⟨γ', TM', E', b'⟩, st', sv.Metadata'.Index', sv.Metadata'.Term', a, t, cs', x',
    srvAuthAtLog C.γr.kv srvAuthSt0 A'', sv.Metadata'.Index'
  isplitr
  · ipureintro; exact beSucc_trans HB HB'
  iframe Hsrv3 Hcv'' HKVf' Hlog' HlbA0
  iframe
  isplitr
  · iexists w; iexact HWA'
  ipureintro
  have hb' : rp.b ≤ A''.length := by have := hgl; omega
  refine ⟨hloop', ?_, ?_, by rw [hci']; exact Int.le_refl _, hlast, ?_, hb', Hty, ?_, HA0b.2⟩
  · rw [hai0, hz0]; omega
  · right; rw [hci', hc00]; simp
  · rw [hgA, hai0, hz0]; omega
  · rw [hci', hai0, hz0]; omega

end proof

section start
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest buckets at the restart's start**: `srvRest` at the backend's log is `srvRestR` at
Go's handed log `P` (`rp = ⟨|P|, A₀⟩`; inside the window, the replay arm at the model's image). -/
theorem srvRestR_start (E : apply.AEnv GF) (γr : ReadNames) (P A₀ : List EntryModel)
    (hP : P <+: A₀) : srvRest (GF := GF) E γr A₀ = srvRestR E γr ⟨P.length, A₀⟩ P := by
  by_cases h : P.length < A₀.length
  · rw [srvRestR_in _ _ _ _ h]
    unfold restReplay
    simp only [List.drop_length, List.foldl_nil]
    rw [srvRestRp_model]
  · have hl := hP.length_le
    have he : P = A₀ := hP.eq_of_length (by omega)
    subst he
    rw [srvRestR_past _ _ _ _ (Nat.le_refl _)]

/-- (restart S4) **Go's start index `|P|`**, the storage snapshot's, is `ai₀ + |P|` at `ai₀ = 0`: room
past the backend's log `A₀` (row 6) and `P <+: A₀`. -/
theorem goIdx_P [GooseExts] (ai₀ : w64) (P A₀ : List EntryModel) (hP : P <+: A₀) (ha : ai₀ = W64 0)
    (hbnd : uint.Z ai₀ + A₀.length + 1 < 2 ^ 64) :
    uint.Z (W64 P.length) = uint.Z ai₀ + P.length := by
  have := hP.length_le
  subst ha
  simp at hbnd ⊢
  word

/-- **`run`'s loop resources at a restart's start** (R2d' probe, step 4): from the restart
form of `applyStartC` (`srvRestartAtR`, at Go's start index `ai = ai₀ + |P|`), `ep`'s fields as `run`
sets them from the storage's snapshot (`server.go:808-814` at `673da07c8`: `appliedi`, `snapi` and
`diskSnapshotIndex` at `ai`, `appliedt` the handed log's last term, `confState` with what
`rnSnapOnceR` gives: `epCsOk`, `epCsAt` at `A₀`, `memSnapLb γs 0`), and the restart point's facts
(`P <+: A₀`; `A₀`'s entries normal or conf changes; room past `A₀`; `c₀ ≤ ai₀`): `applyResR` at `P`. -/
theorem applyResR_start (K : AuthC) (C : ApplyCtx GF) (TM : MetaCI → IProp GF) (P A₀ : List EntryModel)
    (ai at' : w64) (cs : Loc)
    (hP : P <+: A₀) (hai : uint.Z ai = uint.Z C.ai₀ + P.length) (hlt : lastTermIs P at')
    (hc₀ : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hty : ∀ m ∈ A₀, m.typ = W32 0 ∨ m.typ = W32 1)
    (hbnd : uint.Z C.ai₀ + A₀.length + 1 < 2 ^ 64) (hρ : C.ρ.raft = C.γr.raft) :
    isServerC (GF := GF) K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
      epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗
      epConfStateAddr C.ep ↦ cs ∗ epCsOk cs ∗ epCsAt C.ρ.raft A₀ cs ∗
      epDiskSnapAddr C.ep ↦ ai ∗ epMemSnapAddr C.ep ↦ ai ∗
      rnRaftStorageAddr (srvRAddr C.s) ↦□ C.ms ∗ memSnapLb C.γs 0 ∗
      (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ □ mvcc.api.isMvcc kv C.E.γ ∗ ⌜kv = C.E.kv⌝) ∗
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗
      srvRestartAtR K C.s C.γ C.ci C.b C.E C.γr C.ai₀ C.c₀ C.x₀ C.γw A₀ ai ⊢
    applyResR K C ⟨P.length, A₀⟩ P := by
  iintro ⟨#Hsrv, Hai, Hat, Hcsa, #Hcsok, #Hcsat, Hdsi, Hmsi, #Hms, #Hslb, Hkvf, Hwt, Hwtt, Hrs⟩
  iunfold srvRestartAtR at Hrs
  icases Hrs with ⟨%st₀, %a, %t, %f, %g₀, %sa₀, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hwg, Hrdk, Hkv, Hao, Hal, Hkr,
    Hrest, Hap, Hfs, Htok, Hso⟩
  obtain ⟨Hloop, Hce, Hg⟩ := Hok
  icases kvRunM_lbR _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA, Hkr⟩
  have hgh : ghostOf ⟨P.length, A₀⟩ P = A₀ := ghostOf_in ⟨P.length, A₀⟩ P hP
  iunfold applyResR
  iexists ⟨C.γ, TM, C.E, C.b⟩, st₀, ai, at', a, t, cs, C.x₀, sa₀, g₀
  simp only [hgh]
  rw [← srvRestR_start _ _ P A₀ hP]
  isplitr
  · ipureintro; exact beSucc_refl C.γ C.E
  ihave Hcs : epConfState C.ep cs $$ [Hcsa]
  · iunfold epConfState; iframe Hcsa Hcsok
  ihave Hss : srvSnapState C.s C.ep C.ms C.γs ai (W64 0) $$ [Hdsi Hmsi Hfs]
  · iunfold srvSnapState
    iexists ai, ai, f
    iframe Hdsi Hmsi Hfs Hms
    isplitr
    · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
    iExactEq Hslb; rfl
  ihave #HlbA' : srvRLogLb C.ρ.raft A₀ $$ []
  · rw [hρ]; iexact HlbA
  iframe Hsrv Hai Hat Hcs Hcsat Hss Hth Hbe Hca Hlg Hbm Hwg Hrdk Hkv Hao Hal Hkr Hrest Hap HlbA' Hkvf Hwt
  iframe Hwtt Htok Hso
  ipureintro
  have hl := hP.length_le
  refine ⟨Hloop, hai, Or.inr ⟨?_, ?_⟩, ?_, hlt, Hg, Nat.le_refl _, hty, ?_, hbnd⟩
  · omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega
  · rw [← Hce]; omega

end start


section stop
open go_etcd_io.raft.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What `raftNode.stop` takes of the apply thread's resources, in restart form** (swap batch 5:
`StopR.lean`'s `stop_splitR`, in place of the first-start `stop_split` over `applyResC`): the WAL's
apply half and the live transport; the rest kept as `applyResStopR`, which `stopCleanupImage.spec`
takes. -/
theorem stop_split (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) :
    applyResR K C rp A ⊢
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ srvTrStop C.s ∗ applyResStopR K C rp A := by
  unfold applyResR applyResStopR
  iintro ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %hB, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    H10, H11, H12, Hrdk, H13, H14, H15, H16, H17, Hap, Hlb, H18, Hwt, H19, H20, H21, %hp⟩
  iframe Hwt
  isplitl [Hap]
  · iapply srvApRes_trStop $$ Hap
  iexists B, st, ai, at', a, t, cs, x, sa, g
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 Hrdk H13 H14 H15 H16 H17 Hlb H18 H19 H20 H21
  ipureintro; exact ⟨hB, hp⟩

end stop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


set_option hygiene false in
/-- `updateLeadership`'s last step: the stats (`BecomeLeader` unless nil), and the return. -/
local macro "ul_stats" : tactic => `(tactic| (
  (try wp_auto)
  by_cases hst : v.stats = null
  · rw [hst]
    (try wp_auto)
    iapply HΦ'
    itrivial
  · (try wp_auto)
    rw [decide_eq_false hst]
    (try wp_auto)
    wp_apply hBL v.stats $$ []
    · iframe #; ipureintro; exact hst
    (try wp_auto)
    iapply HΦ'
    itrivial))

set_option hygiene false in
/-- `updateLeadership`'s tail: the leader-change notification (if a new leader), the stats. -/
local macro "ul_tail" : tactic => `(tactic| (
  (try wp_auto)
  cases nl
  · ul_stats
  · (try wp_auto)
    wp_apply hN v.leaderChanged $$ []
    · iframe #
    ul_stats))

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
/-- **`run`** at a first start or a restart (R2d'a A10 item 4; swap batch 5, 2026-11-07; restart S4, at Go's start log `P`:
`RunRestart.lean`'s `run.wp_proofR`, in place of the first-start proof): the loop's resources in
restart form (`applyResR` at the restart point `⟨P.length, A₀⟩`, from `applyResR_start`), the batch jobs over
`applyAll.specBatch` (`run_job_body`, with `Hwpend`'s window token borrowed by `winNoMergedSendR`),
the snapshot jobs over `applyAll.specSnapM` (`run_job_snapC`), the stop over `stop_split`,
`raftNode.stop.spec` and `stopCleanupImage.spec`. -/
theorem EtcdServer.run.wp_proofG
    (hSStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hRStop : raftNode.stop.spec (GF := GF) (hG := hG))
    (hCl : stopCleanupImage.spec (GF := GF) (hG := hG))
    (hAB : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG))
    (hAS : EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hGL : EtcdServer.getLead.spec (GF := GF) (hG := hG))
    (hSL : EtcdServer.setLead.spec (GF := GF) (hG := hG))
    (hIL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hBL : v2stats.ServerStats.BecomeLeader.spec (GF := GF) (hG := hG))
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hSCI : EtcdServer.setCommittedIndex.spec (GF := GF) (hG := hG))
    (hRS : raftNode.start.spec (GF := GF) (hG := hG))
    (hRA : raftNode.apply.spec (GF := GF) (hG := hG))
    (hNJ : schedule.NewJob.spec (GF := GF) (hG := hG))
    (hSch : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)) :
    EtcdServer.run.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ dd c
  wp_start as ⟨%hP, Hpre, Htok⟩
  obtain ⟨hM, hRB⟩ := hP
  iunfold isServerRunC at Hpre
  iNamed Hpre
  -- (R2d'a A9) the restart's conjuncts: the backend's ghost log `A₀ = γn.a0`
  iunfold srvRunRestartR at HRr
  icases HRr with ⟨%A₀, %P, %HEr, Hsnap, Hstart, Hloop, Happly⟩
  obtain ⟨HEC, HEγr, Hc0a, Ha0, HPA, HPt, Hty0, Hbnd0⟩ := HEr
  -- (A10 item 5) the raft node's `MsgSnap` bag at `γn` (`isRaftNode`'s), for the merged send's case
  -- `rt ≤ t0`; `Hwpend`'s token and wand
  ihave #Hbagn : srvSnapBagN s γn $$ []
  · iunfold srvSnapBagN
    iframe Hmid
    ihave #Hrn0 := Hrn
    iunfold isRaftNode at Hrn0
    iNamed Hrn0
    iexists _
    iframe Hmsc Hmsci
  iunfold srvWinPend at Hwpend
  icases Hwpend with ⟨%γwp, Hwp, #Hwpw⟩
  icases HWB with ⟨%γp, #HWB, #HWA0, #HWreg⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := (isServerM_C C s γ ci TM E ρ γr).2 $$ Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, -⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsAtM at Hfv'
  icases Hfv' with ⟨#Hlgf, #Hslgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has,
    #Hcl, #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave #Hrf' := Hrf
  iunfold srvRunFieldsAt at Hrf'
  icases Hrf' with ⟨#Hecf, ⟨%γe, #Hecb⟩, #Hscf, #Hscb, #Hdcf, #Hcff, #Hcfs, #Hcpf, #Hcpok, #Hstf,
    #Hlcf, #Hlcn, #Hltg, #Hcinv, #Hgok⟩
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamed Hrn'
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨#Hlg0, Hlr⟩
  · iframe Hlgf; iframe Hlr; iexact Hslgnn
  (try wp_auto)
  -- `s.r.raftStorage.Snapshot()`: the snapshot the server started from
  icases Hsnap with ⟨%ms', #Hms', Hsnap⟩
  icombine Hms Hms' gives %Hmseq
  subst Hmseq
  wp_bind (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
    (Val #()))
  iunfold rnSnapOnceR at Hsnap
  iapply Hsnap
  inext
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok #HcsA0 Hnone #Hmsinv
  -- (2026-10-31, #11) the snapshot's disk side, from the construction's bundle and the node
  icases Hsnapb with ⟨%γt, #Hsro⟩
  ihave #Hsd : srvSnapDisk s γr $$ []
  · iapply srvSnapDisk_of_RO s ci E γr γt Er γn
    iframe Hsro Hrn
  -- (2026-10-30, the repair) the storage's stored snapshot index at least `0`
  imod Hnone with #Hslb0
  obtain ⟨Hsvi, Hsvt, Hpm0n, Hcs0n⟩ := Hsv
  -- the snapshot (raft's `ownSnapM`, read-only: nothing writes it), opened to its metadata `md`
  -- and the metadata's conf state `cs`, which `run` reads directly (the index and term through
  -- the getters, over the metadata's `smOpt`); the pointers are the allocated ones the
  -- contract names (stage R8b: until then non-nil by the conf state having a voter)
  ihave #Hsn' := Hsn
  iunfold ownSnapM at Hsn'
  icases Hsn' with ⟨%ds, %md, %uf, %Hsn0, #HD, #Hd, #HM, #Hm, #Hpb⟩
  icombine HM Hpm0 gives %Hpmeq
  subst Hpmeq
  ihave #Hm' := Hm
  iunfold smOpt at Hm'
  icases Hm' with (⟨%Hmdn, %Hmd0⟩ | #Hm')
  · exfalso; exact Hpm0n Hmdn
  iunfold smPts at Hm'
  icases Hm' with ⟨%cs, %pi, %pt, %uf', %Hmd0, #HC, #Hc, #HI, #HcI, #HT, #HcT, #Hpb'⟩
  icombine HC Hcs0' gives %Hcseq
  subst Hcseq
  have Hcs0 : cs ≠ null := Hcs0n
  (try wp_auto)
  -- the FIFO scheduler: its stop token, its queue `[n₀, p₀]` (`p₀` saving `True`)
  wp_apply hFifo fv.lg iprop(True) $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0, #Hpay⟩
  · iapply zapLoggerOk_ne_null; iexact Hlg0
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hscnn, -⟩
  cases sc with
  | nil => exact absurd rfl Hscnn
  | ok sci =>
  (try wp_auto)
  -- the ready handler
  wp_func_lits
  (try wp_auto)
  ipersist s
  iStructNamedSuffix «$r0» "R"
  iclear _R
  irename getLeadR => getLead
  irename updateLeadR => updateLead
  irename updateLeadershipR => updateLeadership
  irename updateCommittedIndexR => updateCommittedIndex
  ipersist getLead
  ipersist updateLead
  ipersist updateLeadership
  ipersist updateCommittedIndex
  ihave #Hrh : iprop(isReadyHandler «$r0_ptr» (∃ c : w64, srvCommittedOwn γr c) γr) $$ []
  · iunfold isReadyHandler
    iexists _, _, _, _
    iframe getLead updateLead updateLeadership updateCommittedIndex
    isplitr
    · -- `getLead`
      iintro !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hGL s $$ [] as %ld -
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLead`
      iintro %ld !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hSL s ld $$ []
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLeadership`
      iintro %nl !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hIL s fv.memberID $$ [] as %isl -
      · iframe Hlead Hmid
      (try wp_auto)
      ihave #Hlok' := Hlok
      ihave #Hcpok' := Hcpok
      iunfold compactorOk at Hcpok'
      iunfold lessorOk at Hlok'
      icases Hlok' with ⟨%li, %Hli, -, #HDemote, -⟩
      ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
      · iPkgInit
      ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
      · iPkgInit
      ihave #Pt : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
      · iPkgInit
      -- `if !s.isLeader() { .. } else { .. }`, joined (`wp_join`, it only reads `newLeader`): the
      -- notification and the stats after it (`ul_tail`) are verified once
      wp_join at next with [newLeader]
      · cases isl
        · -- not the leader: `Demote`, `Pause`
          simp only [Bool.not_false]
          (try wp_auto)
          rw [Hli]
          (try wp_auto)
          wp_apply HDemote
          (try wp_auto)
          -- `if s.compactor != nil { s.compactor.Pause() }` (M2, S4: a compactor's `Pause`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Pause _ _ _ $$ Hcp with ⟨%ci, %Hci, #HPause⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HPause
          (try wp_auto)
          wp_join_done
        · -- the leader: the election time (if new), `Resume`
          simp only [Bool.not_true]
          (try wp_auto)
          wp_join at next with [newLeader]
          · cases nl
            · (try wp_auto)
              wp_join_done
            · (try wp_auto)
              wp_apply time.wp_Now as %tn -
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Lock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [] as ⟨Hwl, HP⟩
              · iframe Hltg
              iunfold leadTimeP at HP
              icases HP with ⟨%t0, Hlt⟩
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Unlock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [Hwl Hlt]
              · iframe Hwl; iunfold leadTimeP; iexists _; iexact Hlt
              (try wp_auto)
              wp_join_done
          -- `if s.compactor != nil { s.compactor.Resume() }` (M2, S4: a compactor's `Resume`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Resume _ _ _ $$ Hcp with ⟨%ci, %Hci, #HResume⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HResume
          (try wp_auto)
          wp_join_done
      ul_tail
    · -- `updateCommittedIndex`: the writer's half of the committed index
      iintro %ci' %Lc !> %Φ' !> ⟨⟨%c, Hown⟩, #HLc, %HciL⟩ HΦ'
      wp_auto
      wp_apply hGCI s γr (some c) $$ [Hown] as %cci ⟨-, Hown, %Hcci⟩
      · iframe Hcinv; iunfold srvCommittedOwnOpt; iexact Hown
      iunfold srvCommittedOwnOpt at Hown
      have hc : cci = c := Hcci c rfl
      subst hc
      (try wp_auto)
      wp_if_destruct
      · wp_apply hSCI s γr cci ci' Lc (by word) $$ [Hown] as ⟨Hown, #Hca⟩
        · iframe HLc Hcinv; iframe Hown; ipureintro; exact HciL
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists ci'; iexact Hown
      · iunfold srvCommittedOwn at Hown
        ihave #Hlb := monoNatLbOwn_get γr.committed _ _ $$ Hown
        ihave #Hca : iprop(committedAtLeast γr ci') $$ []
        · iapply committedAtLeast_le γr cci ci' (by word)
          iunfold committedAtLeast
          iexact Hlb
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists cci
        iunfold srvCommittedOwn
        iexact Hown
  -- `s.r.start(rh)`: the raft loop, owning the committed index's writer half
  ihave #Hmsinv0 : (letI : MemStorReg GF := ⟨γn.reg⟩; memStorInv γn.ms γn.γs γn.node.cl γn.key)
    $$ []
  · iExactEq Hmsinv; rw [← Hmsγ]
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» P (∃ c : w64, srvCommittedOwn γr c) Hdisk.2.2.1 Hdisk.2.2.2.1
    $$ [Hloop Hrdone Hcomm Hsend Hwtl]
  · rw [HEγr]; iframe Hrh Hrn Hmsinv0 Hslb0; iframe
  (try wp_auto)
  -- `ep`: the snapshot's conf state (the field `cs`, loaded), index and term (the getters, over
  -- the metadata's `smOpt`, read-only: `ai₀` and `at₀`)
  have hGI' := hGI md DFrac.discard sv.Metadata'
  rw [Hsvi] at hGI'
  have hGT' := hGT md DFrac.discard sv.Metadata'
  rw [Hsvt] at hGT'
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGT' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  rw [decide_eq_false Hcs0]
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  -- `expiredLeaseC`: the lessor is non-nil (`lessorOk`)
  ihave #Hlok' := Hlok
  iunfold lessorOk at Hlok'
  icases Hlok' with ⟨%li, %Hli, -, -, #HExp⟩
  rw [Hli]
  (try wp_auto)
  wp_apply HExp as %elc ⟨%γel, #Helc⟩
  (try wp_auto)
  -- the apply thread's resources at the empty log
  iStructNamedSuffix ep "E"
  iclear _E
  irename confStateE => confState
  irename diskSnapshotIndexE => diskSnapshotIndex
  irename memorySnapshotIndexE => memorySnapshotIndex
  irename appliedtE => appliedt
  irename appliediE => appliedi
  -- (R2d'a A10 item 4) the apply thread's resources at the restart's start (`applyResR_start`,
  -- Go's handed log `P` (S4; until then `[]`), the ghost log `A₀`)
  ihave ⟨Hstart, %Hkc0, #HlbA0⟩ : iprop(srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ ρ.wait A₀ (W64 P.length) ∗
      ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝ ∗ srvRLogLb γr.raft A₀) $$ [Hstart]
  · iunfold srvRestartAtR at Hstart
    icases Hstart with ⟨%st₀, %a₀, %t₀, %f₀, %g₀, %sa₀, Hst, %Hst0, Hbe, Happ, Hlr', Hbr, Hwr, Hrdk,
      HKV, Hao, Hal, Hkr, HRS, HAR, Hfs, HtokR, Hso⟩
    ihave Hkr : iprop(kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A₀ x₀ sa₀ ∗
        ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝) $$ [Hkr]
    · rw [← kvRunM_split]; iexact Hkr
    icases Hkr with ⟨Hka0, %Hkc0⟩
    ihave Hkr : kvRunM C.isOn γr ai₀ c₀ A₀ x₀ sa₀ $$ [Hka0]
    · rw [kvRunM_split]; iframe Hka0; ipureintro; exact Hkc0
    icases kvRunM_lbR _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA0, Hkr⟩
    isplitl [Hst Hbe Happ Hlr' Hbr Hwr Hrdk HKV Hao Hal Hkr HRS HAR Hfs HtokR Hso]
    · iunfold srvRestartAtR
      iexists st₀, a₀, t₀, f₀, g₀, sa₀
      iframe Hst Hbe Happ Hlr' Hbr Hwr Hrdk HKV Hao Hal Hkr HRS HAR Hfs HtokR Hso
      ipureintro; exact Hst0
    isplitr
    · ipureintro; exact Hkc0
    iexact HlbA0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  have hρr0 : ρ.raft = γr.raft := by rw [← Hrd]
  ihave HR0 : iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ P) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hstart Hwth]
  · iapply (applyResR_start C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ TM P A₀ (W64 P.length) at₀ cs HPA
      (goIdx_P ai₀ P A₀ HPA Hc0a.2.2 Hbnd0) HPt Hc0a.1 Hty0 Hbnd0 hρr0)
    iframe Hsrv appliedi appliedt confState Hcsok diskSnapshotIndex memorySnapshotIndex Hkvf Hwth Hstart
    isplitr
    · rw [hρr0]; iexact HcsA0
    isplitr
    · rw [← Hmsγ]; iexact Hms
    isplitr
    · iExactEq Hslb0; rfl
    iexists uint.nat ai₀
    rw [← srvWTAt_taken]
    iexact HWA0
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) ∗
      -- (R2d'a A10 item 3) Go's handed log committed, for the stop inside the window
      "#HlbA" ∷ srvRLogLb ρ.raft A) $$ [Happly Hq HR0 Hrunh Hwp]
  · iexists P, [n₀], p₀, iprop(True), iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ P ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp)
    simp only [List.cons_append, List.nil_append]
    iframe
    iframe Hp0
    isplitl [HR0 Hrunh Hwp]
    · iunfold named
      isplitl [HR0]
      · iexact HR0
      isplitl [Hrunh]
      · iExactEq Hrunh; rfl
      iexact Hwp
    isplitr
    · iintro !> ⟨-, H⟩
      iexact H
    rw [hρr0]
    iapply srvRLogLb_mono γr.raft P A₀ HPA $$ HlbA0
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR, #HlbA⟩
  wp_apply (lc := 2) hRA Er γn (srvRAddr s) $$ [] as %apc #Hapc
  · iframe Hrn
  (try wp_auto)
  ihave #Hapc' := Hapc
  iunfold isRNApplyc at Hapc'
  ihave #Hapch : isChan apc γn.ap.chanName toApply $$ []
  · unfold isSspsc; icases Hapc' with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  -- `ap := <-s.r.apply()`: a batch `ce` after `A`, scheduled
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists toApply, inferInstance, inferInstance, inferInstance, inferInstance, apc, γn.ap.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hapch
    iunfold rnApplyTok at Happly
    icases Happly with ⟨%rcv, Hcons, #Hidx⟩
    iapply sspsc_rcv_au γn.ap apc _ _ rcv _ $$ Hapc' [$Hlc1 $Hlc2] Hcons
    inext
    iintro %apv %ok Hrecv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrecv with ⟨Hf, -⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hrecv with ⟨HP, Hcons⟩
    icases rnApplyTok_recv Er γn rcv A apv $$ Hcons Hidx HP with
      (⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, Hnc, HG, #Hrac, #Hcl, #Hrtok⟩ | Hsnp)
    rotate_left
    · -- (R2d'a task 4) the snapshot arm: `run_job_snapC` over `applyAll.specSnapM`, inside
      -- the window or past it, `Hwpend`'s token framed
      icases Hsnp with ⟨%A', %sv, Happly, %Hlen, #Hes, #Hsn, #Hcert, #Hloc, #HC, Hnc, #Hrac, #Hcl,
        #Hrtok⟩
      obtain ⟨hlt, hlenA, h61, hboot, hwa⟩ := Hlen
      icases Hnc with ⟨%γnc, #Hncb, Hnrc⟩
      have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
      have hρC : ρ.raft = γr.raft := by rw [hρ, HEγr]
      have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
      have hgn : γn.node = γr.raft.raft := by rw [← hnd0, hρC]
      have hp0 : γn.pre = [] := Hc0a.2.1
      have ha0 : uint.nat ai₀ = 0 := by rw [Hc0a.2.2]; rfl
      -- the snapshot above the ghost log: past the window Go's `|A| < |A'|`; inside it A8's bound
      -- (S1: derived, `rnRestartOk_winAbove`, recorded at the `Ready`'s receive, carried by `rnApSnap`)
      have hwin : (ghostOf ⟨P.length, A₀⟩ A).length < A'.length := by
        by_cases hw : A₀.length ≤ A.length
        · rw [ghostOf_past ⟨P.length, A₀⟩ A hw]; exact hlt
        · have hab : A₀.length < A'.length := by
            rcases hwa with h | h
            · rw [Ha0] at h; subst h; simp at hw
            · rw [Ha0, hp0, List.nil_append] at h; exact h
          have := ghostOf_length ⟨P.length, A₀⟩ A
          simp only at this
          omega
      ihave #HC' : iprop(srvCM C.isOn ρ E ai₀ c₀ x₀ A') $$ []
      · rw [← HEC]; iexact HC
      (try wp_auto)
      wp_func_lits
      (try wp_auto)
      ipersist ap
      ihave #Hapf := ap
      iStructNamedSuffix Hapf "A"
      ihave #HC'' := HC'
      iunfold srvCM at HC''
      icases HC'' with ⟨-, -, #Hlbr⟩
      imod (schedule.savedProp_alloc iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp))
        with ⟨%post, #Hpost⟩
      wp_apply hNJ γs _ _ iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) $$ [] as %j #Hj
      · iframe #
        iunfold schedule.jobFnSpec
        iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc⟩, HQ, -, -⟩ HΦj
        ihave ⟨Hres, Hhalf, Hwp⟩ := HQR $$ [HQ HR']
        · iframe
        wp_auto
        wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
          (Val #ep_ptr)) (Val #ap_ptr))
        iapply (run_job_snapC hAS ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A A' ap_ptr apv.entries' apv.snapshot' sv
          apv.raftAdvancedC' apv.notifyc' γs γnc γn apv.raftTerm' C hM ha0 Hc0a.1 hp0 hgn hρC
          (by rw [← hρC, hρ]; exact Hnm.2.1) rfl rfl hwin hlenA h61 hboot rfl) $$ [Hrun Hres Hnrc]
        · iframe #
          iframe Hrun Hres Hnrc
        inext
        iintro ⟨Hrun, Hres⟩
        wp_auto
        iapply HΦj
        iframe
      wp_apply hSch sci γs j iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) (some (Ps, pl, post))
        $$ [HR Hnrc Hq] as Hq
      · iframe #
        iframe
        simp only [schedule.schedPre]
        iframe #
        iunfold named at Hq
        iexact Hq
      simp only [schedule.schedPost]
      (try wp_auto)
      wp_for_post
      iframe
      iexists A', Ps ++ [pl], post, iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp), iprop(True)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iframe
      iframe #
      iunfold named
      iintro !> ⟨H, -⟩
      iexact H
    -- (D43 M3) `notifyc` and the driver's view, at the apply side (`rnDv`)
    icases Hnc with ⟨%γnc, #Hncb0, Hnrc⟩
    have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
    have hpre : γn.pre = ρ.raft.pre := by rw [hρ]; exact Hnm.2.1.symm
    have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
    -- (R2d'a A10 item 4) over the ghost log (`rnApR_dv`/`rnApGive_dv`, no `γn.a0 = []`)
    have hp0' : γn.pre = [] := Hc0a.2.1
    have hrp : ρ.raft.pre = [] := by rw [← hpre]; exact hp0'
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (ghostOf ⟨P.length, A₀⟩ (A ++ ce))) $$ []
    · have h := rnApR_dv (GF := GF) γn ρ.raft P.length hrp hnd0 A ce
      simp only [hp0', Ha0, List.nil_append] at h
      rw [← h]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeCC_of_isRaftNode Er γn s $$ Hrn
    have hGv := rnApGive_dv (GF := GF) s γn ρ.raft P.length hrp hnd0 A ce
    simp only [hp0', Ha0, List.nil_append] at hGv
    icases hGv $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
    · iframe Hdyn HG
    have hdvn : rnDv γn ce = none → ∀ m, m ∈ ce → m.typ ≠ W32 1 := by
      intro h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · rw [ite_eq_left hh] at h; cases h
      unfold rnHands at hh
      simp only [Bool.not_eq_true] at hh
      intro m hm hty
      unfold ccIn at hh
      have := List.any_eq_false.1 hh m hm
      simp [hty] at this
    have hdvs : ∀ γn', rnDv γn ce = some γn' → uint.Z c₀ ≤ uint.Z ai₀ ∧
        ρ.raft.raft.rule = srvRule γr.kv.c0 ρ.raft.raft.boot ∧
        ρ.raft.pre = [] ∧ ρ.raft.ai0 = W64 0 := by
      intro γn' _
      obtain ⟨hc, hp0, ha0⟩ := Hc0a
      refine ⟨hc, ?_, by rw [← hpre]; exact hp0, ?_⟩
      · rw [hnd0, Hmd, HEγr]
      · rw [hρ, HEγr, Hkc0.2]; exact ha0
    ihave #HC' : iprop(srvCM C.isOn ρ E ai₀ c₀ x₀ (A ++ ce)) $$ []
    · rw [← HEC]; iexact HC
    (try wp_auto)
    wp_func_lits
    (try wp_auto)
    -- `ap`'s fields, read-only from here on
    ipersist ap
    ihave #Hapf := ap
    iStructNamedSuffix Hapf "A"
    ihave #HC'' := HC'
    iunfold srvCM at HC''
    icases HC'' with ⟨%Hcp, #Hbw, #Hlbr⟩
    obtain ⟨hidx, hok⟩ := Hcp
    ihave #Hbc : iprop(batchCommittedIdx γr ce) $$ []
    · rw [← HEγr]
      iapply batchCommittedIdx_of_last Er.γr ai₀ A ce hidx $$ Hcl
    imod (schedule.savedProp_alloc iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) (ghostOf ⟨P.length, A₀⟩ A)) Q
        iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -, -⟩ HΦj
      ihave ⟨Hres, Hhalf, Hwp⟩ := HQR $$ [HQ HR']
      · iframe
      icases srvRunH_lend γn ρ.raft hnd0 ce $$ Hhalf with ⟨Hrh, Hrhb⟩
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      have hp0 : γn.pre = [] := Hc0a.2.1
      have ha0 : uint.nat ai₀ = 0 := by rw [Hc0a.2.2]; rfl
      ihave #Hrac' : rnAdvChan apv.raftAdvancedC' (letI := srvStor (GF := GF) ρ.raft.raft
          iprop(nodeAppliedLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗ nodeCommitLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗
            srvFrozenRange γn.γs (uint.nat ai₀ + A.length + 1)
              (uint.nat ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms γn.γs (uint.nat ai₀ + 1) (A ++ ce) ∗
            rnWalHanded γn (uint.nat ai₀ + (A ++ ce).length))) $$ []
      · rw [hnd0, show uint.nat ai₀ + (A ++ ce).length = (γn.pre ++ A ++ ce).length by
            simp [hp0, ha0],
          show uint.nat ai₀ + A.length + 1 = (γn.pre ++ A).length + 1 by simp [hp0, ha0],
          show uint.nat ai₀ + 1 = γn.pre.length + 1 by simp [hp0, ha0]]
        iexact Hrac
      have hgn : γr.raft.raft = γn.node := by rw [← HEγr, ← hρ]; exact hnd0
      have hJ := run_job_body hAB ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩
        ⟨P.length, A₀⟩ A ce C hM hRB ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs
        γn.key ha0 Hdisk γn apv.raftTerm' hgn.symm Hc0a.1
        (by have h := hpre.symm.trans hp0; rw [← HEγr, ← hρ]; exact h) rfl (token γwp)
      -- (R2d'a A7, A10 item 5) no merged send at the batch's term while the window is left: past it
      -- nothing; inside it `Hwpend`'s wand at `t0 < rt`, the token borrowed
      ihave #Hwnm : winNoMergedSendR γr.raft.raft s γn.t0 (token γwp)
          (A₀.drop (A ++ ce).length) apv.raftTerm' $$ []
      · iunfold winNoMergedSendR
        by_cases hw : A₀.drop (A ++ ce).length = []
        · ileft; ipureintro; exact hw
        · iright
          iintro !> %hlt Hwtk %id %m %st #Hwid Hwmo #Hwsm
          have hn : (rnLogOf γn (A ++ ce)).length < γn.a0.length := by
            rw [Ha0]
            have h1 : ¬ (A₀.length ≤ (A ++ ce).length) := fun h => hw (List.drop_eq_nil_iff.2 h)
            simp only [rnLogOf, hp0, List.nil_append, List.length_map]
            omega
          iapply Hwpw $$ %apv.raftTerm' %(rnLogOf γn (A ++ ce)).length Hwtk %(And.intro hn hlt) Hrtok %id %m %st
            Hwid Hwmo Hwsm
      ihave #Hmsinv' : (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩;
          memStorInv γn.ms γn.γs γr.raft.raft.cl γn.key) $$ []
      · iExactEq Hmsinv; rw [hgn, ← Hmsγ]
      simp only [run_job_body_match] at hJ
      iapply hJ $$ [Hrun Hres Hnrc Hdv Hrh Hwp]
      · iframe #
        iframe Hrun Hres Hnrc Hdv Hrh Hwp
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hwp, Hres, Hrh⟩
      ihave Hhalf := Hrhb $$ Hrh
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) (ghostOf ⟨P.length, A₀⟩ A)) Q
        iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) (some (Ps, pl, post))
      $$ [HR Hnrc Hdv Hq] as Hq
    · iframe #
      iframe
      simp only [schedule.schedPre]
      iframe #
      iunfold named at Hq
      iexact Hq
    simp only [schedule.schedPost]
    (try wp_auto)
    wp_for_post
    iframe
    iexists (A ++ ce), Ps ++ [pl], post,
      iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨P.length, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp), iprop(True)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    iframe #
    iunfold named
    iintro !> ⟨H, -⟩
    iexact H
  -- `leases := <-expiredLeaseC` (the lease-expiry plan's X1, 2026-11-04; until then dead in every
  -- mode): a slice of expired leases under the server's grant guard (`lessorOk`), so the cluster
  -- grants leases and auth is off; by the lease mode (`lease.runCfg`): `none` grants none (dead),
  -- `mono` lets none expire (dead: `leasesNoExpiry`), `revocable` revokes them
  -- (`revokeExpiredLeases`, through the open premise `srvRevokeOpen`)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoSlice, inferInstance, inferInstance, inferInstance, inferInstance, elc, γel
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Helc
    iapply bag_recv_au γel elc _ _ $$ [$Hlc1 $Hlc2] Helc
    inext
    iintro %ls ⟨%Hnx, #Hls⟩
    ihave %Hg := srvGrantGuard_expired E.lg E.authMode.isOn ls $$ Hls
    ihave %Hlgt := isServerC_lg C s γ ci TM E ρ γr $$ Hsrv
    have hCoff : C.isOn = false := by
      have h2 := Hg.2
      rw [hM, AuthC.mode_isOn] at h2
      exact h2
    obtain ⟨mo, Hmo⟩ := Hslg
    cases mo with
    | none =>
      have h1 : γr.kv.lg = false := by rw [KVNames.lg_eq, lease.runCfg_lm Hmo]; rfl
      have h2 := Hlgt.2 hCoff
      iexfalso; ipureintro
      rw [h1, Hg.1] at h2
      exact Bool.false_ne_true h2
    | mono =>
      iexfalso; ipureintro
      exact Hnx (lease.runCfg_noExpiry Hmo)
    | revocable =>
      -- (revoke-open, 2026-11-06) the revocation with `#Hrvk` and the loop's thread token
      obtain ⟨hlev, hrevo⟩ := lease.runCfg_revoke Hmo
      have hrev := srvRevokeOpen_spec hrevo
      have hlm : ρ.rd.kv.lm = .revocable := by rw [Hlgt.1]; exact lease.runCfg_lm Hmo
      ihave #Hfa : srvFieldsAt s γ ci TM E ρ fv $$ []
      · rw [← srvFieldsAtM_false, ← hCoff]; iexact Hfv
      ihave #Hpe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
      · iPkgInit
      (try wp_auto)
      wp_apply hrev s γ ci TM E ρ fv γr γg γcx v _ ls $$ [Htok] as Htok
      · iframe #; iframe Htok
        ipureintro; exact ⟨hlm, hlev⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists A, Ps, pl, Q, R
      iframe
      iframe #
  -- `err := <-s.errorc`: nothing is sent on it (D19m: `apply` never asks `stopWithDelay` to
  -- stop the server, the transport has no peer that reports this member removed)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, v.errorc, γe
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hecb
    iapply bag_recv_au γe v.errorc _ _ $$ [$Hlc1 $Hlc2] Hecb
    inext
    iintro %err Hf
    iexfalso; iexact Hf
  -- `<-s.stop`: a stop request (`srvStopReq`, `HardStop`'s; R2c-4: until then nothing was sent on
  -- it, D19m): `run` returns, and its deferred shutdown runs (below)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · icases Hscb with ⟨%γst, #Hstb⟩
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stop, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hstb
    iapply bag_recv_au γst v.stop _ _ $$ [$Hlc1 $Hlc2] Hstb
    inext
    iintro %u HSP
    -- (R2b-3d stage 5d) a stop request: `run` returns, and its deferred shutdown runs, with the
    -- stop's slot (R2c-4: `isServerRunC`'s) and the request's readers (R2c-4: until then
    -- `srvShutdownPre`'s)
    iunfold srvStop.slot at Hskeep
    icases Hskeep with ⟨%cfg, %γk, Hkeep, %hST⟩
    iunfold srvStopReq at HSP
    icases HSP with ⟨#HSP, %hsc, #Hdd, Hrds⟩
    obtain ⟨hoff, hcmp⟩ := hsc
    (try wp_auto)
    wp_for_post
    -- the deferred shutdown: `wgMu.Lock(); close(s.stopping); wgMu.Unlock()`
    ihave #Hgok' := Hgok
    iunfold srvGoAttachOk at Hgok'
    icases Hgok' with ⟨%chs, %cx, #Hchs, #Hint, #Hwg, #Hinv, #Hguard, -, -, -⟩
    wp_apply sync.RWMutex.wp_Lock_guard (srvWgMuAddr s) (wgMuP γg) $$ [$Hsync $Hguard]
      as ⟨Hlk, HwP⟩
    iunfold wgMuP at HwP
    icases HwP with ⟨%bo, Hbo, Hsp⟩
    imod goAttach_close γg bo $$ [$Hinv $Hclose $Hbo] with ⟨%hbo, Hbo, Hwz, Hwwt⟩
    subst hbo
    iunfold stopPart at Hsp
    simp only [↓reduceIte]
    (try wp_auto)
    wp_apply wp_stop_chan_close_at chs γg.ch γg.chi iprop(True) $$ [$Hint $Hsp] as #Hsd
    · imodintro; itrivial
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard (srvWgMuAddr s) (wgMuP γg) $$ [$Hsync $Hlk Hbo]
    · iunfold wgMuP; iexists false; iframe Hbo; iunfold stopPart
      simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hsd
    -- `s.cancel()`
    (try wp_auto)
    wp_bind (App (Val #v.cancel) (Val #()))
    ihave #Hcfs' := Hcfs
    iunfold context.cancelSpec at Hcfs'
    iapply Hcfs' $$ []
    · imodintro; itrivial
    inext
    iintro -
    -- `sched.Stop()`: the last job's post, `Q`, and with the loop's `R` the apply thread's resources
    wp_auto_lc 3
    wp_apply +noauto hSStop sci γs (Ps ++ [pl]) $$ [Hstoptok Hq] as ⟨HlastP, -⟩
    · iframe Hstoptok Hq; iframe #; iapply schedule.schedPay_true $$ Hpay
    rw [List.getLast?_concat]
    icases HlastP with ⟨%Psv, #HP, HPl⟩
    iunfold schedule.savedProp at HP Hpl
    ihave #Heq := saved_prop_agree pl DFrac.discard DFrac.discard Psv Q $$ HP Hpl
    ihave HQl : ▷ Q $$ [HPl]
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HPl
    imod (lc_fupd_elim_later (E := ⊤) (P := Q)) $$ Hlc1 HQl with HQ
    ihave ⟨Hres, Hrunh, -⟩ := HQR $$ [HQ HR]
    · iframe HQ HR
    -- `s.wg.Wait()`
    (try wp_auto)
    wp_apply wp_goAttach_Wait s γg $$ [$Hsync $Hwg $Hinv $Hwz $Hwwt] as Hgw
    -- (R2d'a A10 item 3; swap batch 4) the stop in restart form (`stopCleanupImage.spec` over the
    -- ghost log, inside the replay window and past it)
    -- `s.r.stop()`: the WAL's apply half, the transport's stop right (`Er.ST`), the stop claim
    icases stop_split C _ ⟨P.length, A₀⟩ A $$ Hres with ⟨Hwta, Htrs, Hres⟩
    icases (srvStop.keep_split s cfg E γn γk) $$ Hkeep with ⟨Hrp, Hclp, Hcsp, Himp⟩
    icases srvStop.raft_stop s γn γk $$ [$Hrp $Htrs] with ⟨Hsc, HST⟩
    rw [← hST]
    (try wp_auto)
    wp_apply hRStop Er γn (srvRAddr s) A $$ [$Hpkg $Hrn $HST $Hrunh $Hwta $Hsc $Happly]
      as ⟨Hvac, %S, %σ, HrS, Hwc, %Hsh, #Hwcert, #Hdag⟩
    -- the records' commit at least the ghost log: `|A₀|` and `|A|` from `raftNode.stop` (S1: until
    -- then `|A₀|` from the restart data's false row 3, `rnRestartOk_commit`)
    ihave Hrst : iprop(∃ (S : RaftState) (σ : StorContents), raftState γn.node.cl γn.id S ∗
        rnWalClosed γn (srvRAddr s) σ ∗
        ⌜StorageHolds S σ ∧ σ.b ≤ (γn.pre ++ A).length ∧
          (γn.pre ++ ghostOf ⟨P.length, A₀⟩ A).length ≤ σ.commit⌝ ∗
        walSnapCert γn.node.cl σ ∗
        (∃ l', isCommittedLogLb γn.node.cl l' ∗ ⌜σ.b ≤ l'.length ∧ DurAgrees S l'⌝)) $$ [HrS Hwc]
    · iexists S, σ
      iframe HrS Hwc Hwcert Hdag
      ipureintro
      have hp0 : γn.pre = [] := Hc0a.2.1
      have hc1 := Hsh.2.2.1
      have hc2 : A₀.length ≤ σ.commit := by rw [← Ha0]; exact Hsh.2.2.2
      refine ⟨Hsh.1, Hsh.2.1, ?_⟩
      simp only [ghostOf, hp0, List.nil_append, List.length_append, List.length_drop] at hc1 ⊢
      omega
    -- `s.Cleanup()`: the backend closed, the image at the ghost log; (restart S6a) the member id the
    -- raft node's (`srvSnapBagN`'s)
    ihave #Hbg := Hbagn
    iunfold srvSnapBagN at Hbg
    icases Hbg with ⟨#HmidN, -⟩
    (try wp_auto)
    wp_apply hCl C
        (⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ : ApplyCtx GF)
        ⟨P.length, A₀⟩ A Er γg γcx v _ TM cfg dd hM hoff ⟨HEC, HEγr, Hc0a⟩ Hdisk hcmp
      $$ [$Hpkg $Hsrv $Hrn $HmidN $Hrf $Hres $Hclp $Hcsp $Himp $Hdd $Hrds $HSP $Hvac $Hrst $HWB $Hsa
        Hlc2 Hlc3 $HWreg $Hgw] as Himg
    · iapply (lc_split (n := 1) (m := 1)).2; iframe Hlc2 Hlc3
    -- `close(s.done)`, the image escrowed (`srvDoneInv`)
    imod inv_alloc srvStopN ⊤ iprop(srvDiskImage ρ.rd.raft.raft ρ γn.id dd ∨ token c) $$ [Himg]
      with #Hdi
    · inext; ileft; iexact Himg
    (try wp_auto)
    wp_apply +noauto wp_broadcast_chan_close _ γd (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) $$ [$Hdc]
      as -
    · imodintro; iunfold srvDoneInv; iexact Hdi
    (try wp_auto)
    iapply HΦ
    iexact Htok
  iapply BigAndL.bigAndL_nil.2
  itrivial


/-- `run.spec`: `wp_proofG` over `Cleanup`'s and the image's callees (`stop_cleanup_image`). -/
theorem EtcdServer.run.wp_proof
    (hSStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hRStop : raftNode.stop.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hAA : EtcdServer.applyAll.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hGL : EtcdServer.getLead.spec (GF := GF) (hG := hG))
    (hSL : EtcdServer.setLead.spec (GF := GF) (hG := hG))
    (hIL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hBL : v2stats.ServerStats.BecomeLeader.spec (GF := GF) (hG := hG))
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hSCI : EtcdServer.setCommittedIndex.spec (GF := GF) (hG := hG))
    (hRS : raftNode.start.spec (GF := GF) (hG := hG))
    (hRA : raftNode.apply.spec (GF := GF) (hG := hG))
    (hNJ : schedule.NewJob.spec (GF := GF) (hG := hG))
    (hSch : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hRdS : mvcc.api.mvccReaders_split.law (GF := GF))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hStop : mvcc.api.mvccImage_stop.law (GF := GF))
    (Hp : mvcc.api.persistent.law (GF := GF))
    (Hr : mvcc.api.mvccState_reachable.law (GF := GF)) :
    EtcdServer.run.spec (GF := GF) (hG := hG) :=
  EtcdServer.run.wp_proofG hSStop hRStop
    (stop_cleanup_image hCl hOn hSave hPut hUR hID hName hSafe hRdS hCR hStop Hp Hr) hAA.1 hAA.2
    hLg hGI hGT hFifo
    hGL hSL hIL hN hBL hGCI hSCI hRS hRA hNJ hSch

end proof

end EtcdGrove
end Perennial
