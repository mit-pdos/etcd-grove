/-
**The stop arm of `run`'s restart branch, its pieces** (R2d'a A10 item 3, Q27 (i), 2026-11-06; DRAFT:
nothing here is frozen, and no closed theorem imports this file; `notes/restart-plan.md`, "R2d'a A10
item 3"). Lean-first (no Rocq counterpart).

At a stop past the replay window `run`'s restart branch has `applyResC` (`applyResR_past`) and takes
the frozen path (`stop_split`, `stopCleanupImage.spec`). Inside the window (Go's log `A` shorter than
the backend's `A₀`) the ghost rows are at `A₀`, and the image is at the backend's index:
* `applyResStopR`, `stop_splitR`: `applyResStop`/`stop_split` over `applyResR`;
* `restReplay_bk`, `restLeasesWith_bk_congr`: the replay changes only the members, so the backend's
  rest buckets stay the model's at `A₀`;
* `stopCleanupImageR.spec`, `stop_cleanup_imageR`: `stopCleanupImage.spec` inside the window, with
  `A <+: A₀` from both logs committed (`srvRLogLb_prefix`), the image at `A₀` and the records' commit
  at least `|A₀|` (from `raftNode.stop.spec`'s unchanged post and the restart data,
  `rnRestartOk_commit`; `run` reads the restart data from the loop's token before the start,
  `rnLoopTok_restartOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopShutdown
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply thread's resources at the stop, in restart form, but what `raftNode.stop` takes**
(DRAFT): `applyResR`'s without the WAL's apply half (`rnWalTokA`) and the membership resource
(`srvApRes`, whose live transport goes to `Er.ST`), as `applyResStop` is `applyResC`'s. -/
def applyResStopR (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState) (g : w64),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerC K C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    epCsAt C.ρ.raft (ghostOf rp A) cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKVC K C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr g ∗ appliedLogAt C.γr g x.log ∗ kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A) x sa ∗
    srvRestR B.E C.γr rp A ∗ srvRLogLb C.ρ.raft rp.A₀ ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ txn.isKV kv B.E.s B.E.γ) ∗
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

/-- **What `raftNode.stop` takes of the apply thread's resources, in restart form** (`stop_split`'s):
the WAL's apply half and the live transport. -/
theorem stop_splitR (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) :
    applyResR K C rp A ⊢
      rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗ srvTrStop C.s ∗ applyResStopR K C rp A := by
  unfold applyResR applyResStopR
  iintro ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %hB, H1, H2, H3, H4, H5, H6, H7, H8, H9,
    H10, H11, H12, H13, H14, H15, H16, H17, Hap, Hlb, H18, Hwt, H19, H20, H21, %hp⟩
  iframe Hwt
  isplitl [Hap]
  · iapply srvApRes_trStop $$ Hap
  iexists B, st, ai, at', a, t, cs, x, sa, g
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 Hlb H18 H19 H20 H21
  ipureintro; exact ⟨hB, hp⟩

/-- The replay changes only the members: its buckets are the backend log's model's. -/
theorem restReplay_bk (γr : ReadNames) (rp : RestartPt) (G : List EntryModel) :
    (restReplay γr rp G).bk = (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀)).bk := by
  unfold restReplay
  rw [fold_restEntryV2]

/-- The leases' records written over two images with the same buckets have the same buckets. -/
theorem restLeasesWith_bk_congr (f : w64 → w64) (ids : List w64) (r r' : apply.RestM)
    (h : r.bk = r'.bk) : (apply.restLeasesWith f ids r).bk = (apply.restLeasesWith f ids r').bk := by
  unfold apply.restLeasesWith
  induction ids generalizing r r' with
  | nil => exact h
  | cons id ids ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold apply.restGrantT
    rw [apply.RestM.putIn_bk, apply.RestM.putIn_bk, h]

end laws

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Cleanup()` at a stop inside the replay window, and the image** (DRAFT; `stopCleanupImage.spec`
in restart form): the apply thread's resources at Go's log `A` in restart form (`applyResStopR`), Go's
log committed (`srvRLogLb`, so a prefix of the backend's `A₀`), and the records' stored commit at
least `|A₀|`; the image at the backend's log `A₀` and its index. The rest as
`stopCleanupImage.spec`'s. -/
abbrev stopCleanupImageR.spec : Prop :=
  ∀ (K : AuthC) (C : ApplyCtx GF) (rp : RestartPt) (A : List EntryModel) (Er : RNEnv GF)
    (γg : GoNames) (γcx : context.ContextNames) (v : RunFields) (SP : IProp GF)
    (TM : MetaCI → IProp GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (dd : GoString),
    C.E.authMode = K.mode → C.E.authOn = false →
    (Er.C = srvCM K.isOn C.ρ C.E C.ai₀ C.c₀ C.x₀ ∧ Er.γr = C.γr ∧
      (uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.rn.pre = [] ∧ C.ai₀ = W64 0)) →
    storage.diskOk →
    C.E.cmp = false →
    -- inside the replay window
    A.length < rp.A₀.length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerC K C.s C.γ C.ci TM C.E C.ρ C.γr ∗
        isRaftNode Er C.rn (srvRAddr C.s) ∗
        srvRunFieldsAt C.s C.γr γg γcx v SP ∗
        applyResStopR K C rp A ∗ srvRLogLb C.ρ.raft A ∗
        srvStop.cleanupPart C.s C.E ∗ srvStop.censusPart C.s C.E ∗ srvStop.imagePart C.s cfg C.rn ∗
        srvDataDir C.s dd ∗ ([∗list] _x ∈ List.replicate (64 + 64) (), mvcc.storeReader C.E.s C.E.γ) ∗
        srvBootApplied C.ρ ∗
        nodeVacant C.rn.node.cl C.rn.id ∗
        (∃ (S : RaftState) (σ : StorContents), raftState C.rn.node.cl C.rn.id S ∗
          rnWalClosed C.rn (srvRAddr C.s) σ ∗
          ⌜StorageHolds S σ ∧ σ.b ≤ (C.rn.pre ++ A).length ∧ rp.A₀.length ≤ σ.commit⌝ ∗
          -- (R2d, Q14 (a), DRAFT) the records' snapshot certificate (`raftNode.stop`'s)
          walSnapCert C.rn.node.cl σ) ∗
        srvWTPool C.E C.wt ∗ isServerApplyAll C.s C.γr ∗ £ 2 ∗
        -- (H2, 2026-11-05) the budget's register at `GoAttach`'s receipts, and `Wait` returned
        dghostVar C.wt.reg DFrac.discard (some γg.run) ∗ goWaited γg }}
      (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
    {{ RET #(); srvDiskImage C.ρ.rd.raft.raft C.ρ C.rn.id dd }}


theorem stop_cleanup_imageR (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    stopCleanupImageR.spec (GF := GF) (hG := hG) := by
  intro K C rp A Er γg γcx v SP TM cfg dd hM hoff hEr hdisk hcmp hwin
  iintro %Φ ⟨#Hpkg, #Hsrv0, #Hrn, #Hrf, Hres, #HlbA, Hclp, Hcsp, Himp, #Hdd, Hrds, #Hba, Hvac,
    ⟨%S, %σ, Hrst, Hwc, %hσ, #Hσc⟩, #Hpool, #Hsa, Hlc, #Hreg, Hwd⟩ HΦ
  -- auth off
  cases K with
  | on γa =>
    exfalso
    simp [apply.AEnv.authOn, hM, AuthC.mode, auth.AuthMode.isOn] at hoff
  | off => ?_
  unfold applyResStopR
  icases Hres with ⟨%B, %st, %ai0g, %at', %a, %t, %cs, %x, %sa, %ai, %hB, #Hsrv, -, -, -, -, -, Hst, -, -,
    -, Hbr, -, HKV, Hao, #Hlog, Hkr, HRs, #HlbA0, #Hkv, -, -, Hso, %hp⟩
  -- (R2d'a A10 item 3) inside the window Go's log is a prefix of the backend's: the ghost log is
  -- the backend's (`ghostOf_in`), the ghost index `ai` (`g`) at it
  ihave %hpc := srvRLogLb_prefix C.ρ.raft A rp.A₀ $$ [HlbA HlbA0]
  · iframe HlbA HlbA0
  have hAin : A <+: rp.A₀ := by
    rcases hpc with h | h
    · exact h
    · exact absurd h.length_le (by omega)
  have hG : ghostOf rp A = rp.A₀ := ghostOf_in rp A hAin
  rw [hG, srvRestR_in B.E C.γr rp A hwin]
  rw [hG] at hp
  obtain ⟨hc0a, hpre, hai0⟩ := hEr.2.2
  have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0a; word
  -- the current backend's environment is the start's on another backend
  obtain ⟨-, pB, PB, fB, cB, ROB, RWB, hEB⟩ := hB
  have hBcmp : B.E.cmp = false := by rw [hEB]; exact hcmp
  have hBs : B.E.s = C.E.s := by rw [hEB]; rfl
  have hBbe : B.E.γbe = C.E.γbe := by rw [hEB]; rfl
  have hBam : B.E.authMode = .off := by rw [hEB]; exact hM
  have hrdr : mvcc.storeReader (GF := GF) C.E.s C.E.γ = mvcc.storeReader B.E.s B.E.γ := by
    rw [hEB]; rfl
  -- the apply thread's view of the server: its backend `d`, with its hooks, not compacting
  have hS : isServerC (GF := GF) AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr ⊢
      isServer C.s B.γ C.ci B.TM B.E C.ρ C.γr :=
    (isServerM_C AuthC.off C.s B.γ C.ci B.TM B.E C.ρ C.γr).2
  ihave #HsrvI := hS $$ Hsrv
  ihave #Hsrv' := Hsrv
  iunfold isServerC at Hsrv'
  icases Hsrv' with ⟨%hρ, #HCI, ⟨%vf, #Hf⟩, #Hat, -⟩
  iunfold srvFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hbh⟩
  iunfold srvBeHooked at Hbh
  icases Hbh with ⟨%d, %bh, %lgh, %Hd, -, #Hbhk, #HhkAt, #HB⟩
  obtain ⟨hkb, hcK, hhP⟩ := Hd
  obtain ⟨-, -, -, γB, HH, hRO, -, d', _al, _stl, _lp, hkb', hγB, -, hcm⟩ := Henv
  rw [hkb] at hkb'
  obtain rfl := Option.some.inj hkb'
  subst hγB
  have hdcm : d.cm = false := hcm.trans hBcmp
  have hnk : ¬ mvcc.kbCmpM B.E.γ.kb := by rw [hkb]; simp [mvcc.kbCmpM, hdcm]
  iunfold srvAtomicsC at Hat
  icases Hat with ⟨-, -, #Hki⟩
  iunfold srvKVInvsC at Hki
  icases Hki with ⟨-, -, #Hrl, -⟩
  -- the start's backend does not compact either (`srvKeepRdN`'s count)
  ihave #Hsrv0' := Hsrv0
  iunfold isServerC at Hsrv0'
  icases Hsrv0' with ⟨-, -, ⟨%vf0, #Hf0⟩, -⟩
  iunfold srvFieldsAtM at Hf0
  icases Hf0 with ⟨-, -, -, -, -, %Henv0, -⟩
  obtain ⟨-, -, -, -, -, -, -, d0, -, -, -, hkb0, -, -, hcm0⟩ := Henv0
  have hnj0 : mvcc.nJobRd C.E.γ.kb = 0 := by
    rw [hkb0]; simp [mvcc.nJobRd, hcm0, hcmp]
  have hnjB : mvcc.nJobRd B.E.γ.kb = 0 := by
    rw [hkb]; simp [mvcc.nJobRd, hdcm]
  -- the lessor's stop right and the auth store's closer (the slot's)
  icases srvStop.cleanup_pieces C.s C.E $$ Hclp with ⟨⟨%lp, #Hlpa, Hlst⟩, #Hauth⟩
  ihave Hac := Hauth $$ %hoff
  icases Hac with ⟨%stl, #Hstla, #Hacl⟩
  -- the snapshot path's resources at the current backend: its stop channels, the constructors'
  -- half of the open token, the KV's closer, the backend's file and its directory entry
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, -, -, -, Hsr⟩
  iunfold srvSnapRes at Hsr
  icases Hsr with ⟨%d2, %al2, %dd2, %hd2, #Hsch, Hhalf, -, Hkc, #Hdd2, Hpath, #Hbf⟩
  rw [hkb] at hd2
  obtain rfl := Option.some.inj hd2
  have hq : srvOpenQ B.E.authMode = (1 : Qp).half := by rw [hBam]; rfl
  rw [hq, srvKVCloserW_off C.s B.E hnk]
  iunfold srvKVCloser at Hkc
  icases Hkc with ⟨%wsl, #Hkva, Hwcl⟩
  -- the watchable store at the KV field
  icases Hkv with ⟨%kv, #Hkva', #HisKV⟩
  icombine Hkva Hkva' gives %hkveq
  iunfold txn.isKV at HisKV
  icases HisKV with (⟨%hk1, -, -⟩ | ⟨%ws, %γw, %hk2, #Hws⟩)
  · exfalso
    rw [← hkveq] at hk1
    simp [interface.mkOk] at hk1
    have hne : go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty ≠
        go_etcd_io.etcd.server.v3.storage.mvcc.store.ty := by
      unfold go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty
        go_etcd_io.etcd.server.v3.storage.mvcc.store.ty
      simp
    exact hne hk1.1
  obtain ⟨hk2, hγw⟩ := hk2
  rw [← hkveq] at hk2
  have hws : wsl = ws := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at hk2
    simpa [intoVal_eq_iff] using hk2
  subst hws
  -- the apply thread's KV resources
  icases srvApplyKVC_coreA AuthC.off C.s B.E C.γw x sa $$ HKV with ⟨%ua, Hcore, -, -⟩
  iunfold srvApplyKVCore at Hcore
  icases Hcore with ⟨-, -, Hakv, Hbo, -, -⟩
  iunfold apply.applyKV at Hakv
  icases Hakv with ⟨%pu, -, -, Hko, -⟩
  iunfold apply.kvOwn at Hko
  icases Hko with ⟨HsrA, Hkw, -, -, Hwo⟩
  iunfold txn.kvWriter at Hkw
  icases Hkw with ⟨Hsw, Hwl, Hfr⟩
  ihave %Hwf := soleWriter_idxWf B.E.γ x.log $$ Hsw
  iunfold txn.wlogOwn at Hwl
  icases Hwl with ⟨-, Hpin⟩
  iunfold mvcc.writerOwn at Hwo
  icases Hwo with ⟨HrtA, Hret⟩
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d3, %hd3, Hbe, Hg, -, HbPl⟩
  rw [hkb] at hd3
  obtain rfl := Option.some.inj hd3
  iunfold backend.bkRPool at HbPl
  icases HbPl with ⟨-, HoPs⟩
  rw [hBbe]
  -- the monitor's read token (H2)
  icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc1, Hlc2⟩
  ihave #Hrf' := Hrf
  iunfold srvRunFieldsAt at Hrf'
  icases Hrf' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hgok⟩
  iunfold srvGoAttachOk at Hgok
  icases Hgok with ⟨%gch, %gc, -, -, -, #Hginv, -⟩
  imod stop_monitorRT C.E C.wt γg d $$ [Hlc1 Hg Hwd] with ⟨Hg, HrtM⟩
  · iframe Hlc1 Hpool Hginv Hreg Hwd Hg
  -- the census (gap 4): the slot's readers with the compactor's, the caller's 128, the apply
  -- thread's own, at the current names
  iunfold srvRunFieldsAt at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, #Hcpa, #Hcpok, -⟩
  icases srvStop.census_readers C.s C.E v.compactor hcmp $$ [Hcsp Hcpa] with ⟨%hcp, Hcr⟩
  · iframe Hcsp Hcpa
  ihave Hrs := stop_rep_join _ _ _ $$ Hcr Hrds
  rw [hrdr]
  ihave Hrs := stop_rep_cons1 _ _ $$ Hrs HsrA
  ihave #HisSt : mvcc.isStore B.E.s B.E.γ $$ [Hws]
  · rw [← hγw]; iapply mvcc.isWatchableStore_isStore; iexact Hws
  have hm : srvKeepRdN C.E.γ + 1 + (64 + 64) + 1 + mvcc.wsLoopN + 2 =
      backend.rdStockN - mvcc.nJobRd B.E.γ.kb := by
    have hL : mvcc.wsLoopN = 2 := rfl
    simp only [srvKeepRdN, hnj0, hnjB, backend.rdStockN_val, hL]
  ihave Hwand := stop_census B.E.s B.E.γ d hkb (srvKeepRdN C.E.γ + 1 + (64 + 64) + 1) hm
    $$ [Hlc2 HisSt Hfr Hrs Hret HrtA HrtM Hhalf HoPs]
  · iframe Hlc2 HisSt Hfr Hrs Hret HrtA HrtM Hhalf HoPs
  ihave Hwand' : (mvcc.wsCloseRes B.E.s γw.st ={⊤}=∗ backend.bOpen d.γB 1) $$ [Hwand]
  · rw [hγw]; iexact Hwand
  ihave Hwcm : mvcc.wsCloserM wsl B.E.s γw.st (-1) $$ [Hwcl]
  · rw [hγw]; iapply (mvcc.wsCloserM_off _ _ _ _ hnk).2; iexact Hwcl
  -- the stop commit's request (`commitReq_freeze`)
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hcipkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Hnh := isBackendNH_of_hooksAt d.γB d.P (mvcc.lateWD d)
    (batchLockInv B.γ (metaTM d.γB d.P)) d.be (storage.hooksIface bh) $$ [HB HhkAt]
  · iframe #
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #Hci, #Hinv⟩
  ihave #Hreq := commitReq_freeze hOn hSave hPut hUR hID hName hSafe B.γ C.ci d.γB d.P
    (mvcc.lateWD d) d.be bh lgh hcK hhP st hp.1.1
    $$ [Hspkg Hbpkg Hschpkg Hcipkg Hbhk Hnh HB Hci Hinv]
  · iframe #
  iunfold srvStopChans at Hsch
  icases Hsch with ⟨-, #HSC⟩
  -- `s.Cleanup()`
  iapply wp_fupd
  wp_apply hCl C.s lp wsl B.E.s γw (-1) stl iprop(True) C.E.γbe d _ (mvcc.lateWD d)
      (batchLockInv B.γ (metaTM d.γB d.P)) v.compactor (applyThread B.γ st) (freezeY B.γ st)
    $$ [Hlst Hwcm Hbr Hbe Hg Hwand' Hst]
    as ⟨-, -, -, -, HY, %D, Hsv, Hfile⟩
  · rw [hcp]
    iframe Hlpa Hlst Hkva Hws Hwcm Hstla Hacl Hbr Hbe Hg HB HSC Hwand' Hst Hreq Hcpa Hcpok
  -- the stopped backend's data observed: the image of the applied log at `ai`
  have hci : ciEff B.γ st.k = ai := by
    obtain ⟨-, -, hJ, hle, -⟩ := hp
    rcases hJ with h | ⟨-, h⟩
    · rw [h, hc00] at hle ⊢; word
    · word
  have hRB : ∀ n ∈ restBuckets, d.P.RB n = true := fun n hn => by
    simp [mvcc.KBReal.P, hn]
  ihave ⟨%f, %Hfb, HRs, -, -, -⟩ := srvRestRp_open B.E C.γr rp.A₀ (restReplay C.γr rp A) $$ HRs
  rw [hRO]
  iunfold srvRestOwnH at HRs
  icases HRs with ⟨Hro, -⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrc, Hrn', -, -⟩
  -- the replay changes only the members: the backend's buckets are the model's at `A₀`
  rw [restLeasesWith_bk_congr f (srvIds B.E (appliedTable C.γr rp.A₀).ids) _
    (restModel C.γr.kv.c0 C.γr.raft.raft.boot (C.γr.raft.pre ++ rp.A₀)) (restReplay_bk C.γr rp A)]
  ihave %hobsM := stop_mergedObsP B.γ B.E C.γr ai rp.A₀ x d f st D hkb hcK hRB hcm hdcm hci Hwf Hfb
    $$ [HY Hrc Hrn' Hpin Hsv]
  · iframe HY Hrc Hrn' Hpin Hsv
  have hobs := mergedObs_of_M hBam hobsM
  -- the KV names' start values
  have ekr : kvRunM (GF := GF) AuthC.off.isOn C.γr C.ai₀ C.c₀ rp.A₀ x sa = kvRun C.γr C.ai₀ C.c₀ rp.A₀ x :=
    rfl
  rw [ekr]
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %hk0⟩
  iunfold isServerApplyAll at Hsa
  icases Hsa with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
  have hc0' : C.γr.kv.c0 = W64 0 := hk0.1.trans hc00
  imod merged_imageAt C.s B.γ C.ci B.TM B.E C.ρ C.γr ai rp.A₀ x D ⟨hc0', Hlog0⟩ $$ [HsrvI Hka]
    with ⟨Hka, %himg⟩
  · iframe HsrvI Hka; ipureintro; exact hobs
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, -⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, -⟩
  -- raft's names: the raft wrapper's
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  icases Hrn' with ⟨%_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, %_, #Henv, -⟩
  iunfold rnEnvOk at Henv
  icases Henv with ⟨-, %hraft, -⟩
  have hγ : C.γr.raft.raft = C.rn.node := by rw [← hEr.2.1]; exact hraft.1
  have hpre' : C.γr.raft.pre = [] := by rw [← hEr.2.1, hraft.2.1, hpre]
  have hai : uint.nat ai = rp.A₀.length := by
    have h1 := hp.2.2.2.2.2.1; rw [hai0] at h1; word
  -- the bootstrap log applied (the stop request's evidence)
  ihave #Hrl' := Hrl
  iunfold srvRaftLogInv at Hrl'
  icases Hrl' with ⟨-, #Hcl, -⟩
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, %HbL, -⟩
  iunfold srvBootApplied at Hba
  icases Hba with ⟨%vb, #Hvb, %hvb⟩
  rw [hρ] at hvb
  iunfold appliedAtLeast at Hvb
  iunfold srvAppliedOwn at Hao
  icases Hao with ⟨Hao, -⟩
  rw [hρ]
  ihave %hle := monoNatLbOwn_valid C.γr.applied _ _ _ $$ Hao Hvb
  have hboot : C.γr.raft.raft.boot.length ≤ rp.A₀.length := by rw [← hai]; omega
  -- the configuration point
  imod stop_imageConf C.γr.raft C.γr.kv rp.A₀ D ai hpre' hai hc0' hboot himg $$ [Hrl HA]
    with ⟨#Hconf, %hconf⟩
  · iframe Hrl HA
  -- the registry's authority and the WAL's files
  icases srvStop.image_inputs C.s cfg C.rn dd $$ [Himp Hdd] with ⟨⟨%M, HM⟩, %st', #Hst', %hwd⟩
  · iframe Himp Hdd
  iunfold rnWalClosed at Hwc
  icases Hwc with ⟨%st2, #Hst2, Hw⟩
  iunfold rnWalClosedW at Hw
  icombine Hst' Hst2 gives %hsteq
  subst hsteq
  -- the backend's file
  iunfold srvDataDir at Hdd
  icases Hdd with ⟨#Hdd1, -⟩
  icombine Hdd1 Hdd2 gives %hddeq
  subst hddeq
  icases Hfile with (⟨%path, #Hbf2, Hfh⟩ | %hbad)
  rotate_left
  · exact absurd hdisk.2.1.2.2.2 hbad
  ihave %hpath := backend.bFile_agree d.γB (config.backendPathOf dd) path $$ [Hbf Hbf2]
  · iframe Hbf Hbf2
  subst hpath
  -- the image
  imodintro
  iapply HΦ
  iunfold srvDiskImage
  iexists S, σ, ai, rp.A₀, D, Membership.simple C.γr.raft.raft.cfg, M
  rw [hρ] at *
  iunfold srvFiles
  rw [← hwd, ← hγ]
  have h1 := hp.2.2.2.2.2.1
  have h2 := hσ.2.1
  have h3 := hσ.2.2
  have hAl := hAin.length_le
  rw [hpre] at h2
  ihave Hσc := wal.stopImage_intro _ S σ ai hσ.1 (by simp at h2; omega) (by omega)
    $$ Hσc
  iframe Hvac Hrst HA HM Hpath Hfh Hconf Hw Hσc
  ipureintro
  refine ⟨⟨rfl, hc0'⟩, ⟨by rw [hk0.2]; exact h1, by rw [hpre'] at himg ⊢; exact himg⟩,
    by rw [HbL]; omega, hconf⟩
end proof

end EtcdGrove
end Perennial
