/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/NewRaft.lean (241f27e).
-/
/-
The proof of `raft.NewRaft`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.NewRaft
public import Dsverify.Spec.github_com.hashicorp.raft.ValidateConfig
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__restoreFromCommittedLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setLatestConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__setCommittedConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.DecodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.max
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__goFunc
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__run
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runFSM
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__runSnapshots
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processHeartbeat
public import Perennial.Proof.sync
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftBase
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftBoot
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftScan

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

/-- An existential of fractional predicates whose witnesses agree is fractional (a copy of
Perennial's `IrisLib/BI.lean` lemma, whose module is not built in this pin). -/
theorem fractional_exists_agree' {PROP : Type _} [BI PROP] {X : Type _} (Φ : X → Qp → PROP)
    (hfrac : ∀ x, Fractional (Φ x)) (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

instance typedPointsto_own_fractional' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    Fractional (fun q : Qp => typedPointsto (GF := GF) l v (DFrac.own q)) where
  fractional q1 q2 := typedPointsto_frac_add l v q1 q2

instance leaderLockP_fractional (r : Loc) : Fractional (leaderLockP (GF := GF) r) := by
  unfold leaderLockP
  apply fractional_exists_agree'
  · intro a
    apply fractional_exists_agree'
    · intro id; infer_instance
    · intro x y q1 q2
      iintro ⟨⟨_, H1⟩, ⟨_, H2⟩⟩
      icombine H1 H2 gives %h
      ipureintro; exact h
  · intro x y q1 q2
    iintro ⟨⟨%id1, H1, _⟩, ⟨%id2, H2, _⟩⟩
    icombine H1 H2 gives %h
    ipureintro; exact h

instance lastContactP_fractional (r : Loc) : Fractional (lastContactP (GF := GF) r) := by
  unfold lastContactP
  apply fractional_exists_agree'
  · intro t; infer_instance
  · intro x y q1 q2
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %h
    ipureintro; exact h

instance observersP_fractional (γ : GNames) (rc : RCtx GF) (i : SID) (r : Loc) :
    Fractional (observersP (GF := GF) γ rc i r) := by
  unfold observersP
  apply fractional_exists_agree'
  · intro m
    apply fractional_exists_agree'
    · intro mv
      have := ownMap_fractional (GF := GF) m mv
      refine ⟨fun p q => ?_⟩
      constructor
      · iintro ⟨H1, H2, #H3⟩
        icases (typedPointsto_frac_add (GF := GF) _ m p q).1 $$ H1 with ⟨H1a, H1b⟩
        icases (this.fractional p q).1 $$ H2 with ⟨H2a, H2b⟩
        iframe; iframe #
      · iintro ⟨⟨H1a, H2a, #H3⟩, ⟨H1b, H2b, _⟩⟩
        isplitl [H1a H1b]
        · iapply (typedPointsto_frac_add (GF := GF) _ m p q).2; iframe
        isplitl [H2a H2b]
        · iapply (this.fractional p q).2; iframe
        iexact H3
    · intro x y q1 q2
      iintro ⟨⟨_, H1, _⟩, ⟨_, H2, _⟩⟩
      iapply ownMap_agree $$ [H1 H2]
      iframe
  · intro x y q1 q2
    iintro ⟨⟨%mv1, H1, _⟩, ⟨%mv2, H2, _⟩⟩
    icombine H1 H2 gives %h
    ipureintro; exact h

theorem pkgGlobals_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ pkgGlobals (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft

/-- `r.setLeader("", "")` on the fresh `Raft` (its `leaderLock` used at the low level, before
its invariant is allocated): the leader fields are already empty, so nothing is observed. -/
theorem wp_setLeader_init (r : Loc) (γl : sync.rwmutex.RWMutexNames) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       sync.rwmutex.isRWMutex (r.[Raft, go!"leaderLock"]) γl (nroot.@"rw") ∗
       sync.rwmutex.ownRWMutex γl (.RLocked 0) ∗
       r.[Raft, go!"leaderAddr"] ↦ ([] : ServerAddress) ∗ r.[Raft, go!"leaderID"] ↦ ([] : ServerID) }}
      (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLeader"))
        (Val #([] : ServerAddress))) (Val #([] : ServerID)))
    {{ RET #(); sync.rwmutex.ownRWMutex γl (.RLocked 0) ∗
       r.[Raft, go!"leaderAddr"] ↦ ([] : ServerAddress) ∗ r.[Raft, go!"leaderID"] ↦ ([] : ServerID) }} := by
  wp_start as ⟨#His, Hst, Ha, Hid⟩
  wp_auto
  wp_apply_core (sync.rwmutex.RWMutex.wp_Lock γl _ (nroot.@"rw")) $$ [] [-]
  · iframe #
    iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iexists _
  iframe Hst
  iintro %_ Hst
  imod Hclose with _
  imodintro
  wp_auto
  wp_apply_core (sync.rwmutex.RWMutex.wp_Unlock γl _ (nroot.@"rw")) $$ [] [-]
  · iframe #
    iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  iframe Hst
  iintro Hst
  imod Hclose with _
  imodintro
  wp_auto
  wp_end

theorem monoNatAuth_halves (γn : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γn 1 n ⊢
      monoNatAuthOwn γn (1 : Qp).half n ∗ monoNatAuthOwn γn (1 : Qp).half n := by
  have h := (monoNatAuthOwn_fractional (GF := GF) γn n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

open Iris.MonoNat in
theorem monoNatAuth_lb_le (γn : GName) (q : Qp) (n m : Nat) :
    monoNatAuthOwn (GF := GF) γn q n ∗ monoNatLbOwn γn m ⊢ monoNatAuthOwn γn q n ∗ ⌜m ≤ n⌝ := by
  unfold monoNatAuthOwn monoNatLbOwn
  iintro ⟨H1, #H2⟩
  icombine H1 H2 gives %Hvalid
  iframe H1
  ipureintro; exact ((both_dfrac_valid _ _ _).mp Hvalid).2

/-- (D33) The zero `atomic.Pointer[Configuration]` holds `nil`. -/
theorem ownPointer_zero_cfg (u : Loc) :
    typedPointsto (GF := GF) u (zero_val (sync.atomic.Pointer Configuration)) (DFrac.own 1) ⊢
      sync.atomic.ownPointer (T' := Configuration) u (DFrac.own 1) null := by
  rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; exact .rfl


/-- The bootstrapped log store's map: the genesis at index 1. -/
theorem genesisStore_m (g : Entry) (k : Nat) :
    (LogAbs.empty.store 1 [g]).m.lookup k = if k = 1 then some g else none := by
  simp only [LogAbs.store, LogAbs.empty, LogAbs.ins, GMap.lookup_insert_eq_iff]
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; rfl

theorem genesisStore_hi (g : Entry) : (LogAbs.empty.store 1 [g]).hi = W64 1 := by
  simp [LogAbs.store, LogAbs.empty]

set_option pp.maxSteps 2000000 in
set_option maxHeartbeats 4000000 in
theorem github_com.hashicorp.raft.NewRaft.wp_proof
    (wp_ValidateConfig : github_com.hashicorp.raft.ValidateConfig.spec (GF := GF) (hG := hG))
    (wp_restoreSnapshot : github_com.hashicorp.raft.Raft.restoreSnapshot.spec (GF := GF) (hG := hG))
    (wp_restoreFromCommittedLogs :
      github_com.hashicorp.raft.Raft.restoreFromCommittedLogs.spec (GF := GF) (hG := hG))
    (wp_setLatestConfiguration :
      github_com.hashicorp.raft.Raft.setLatestConfiguration.spec (GF := GF) (hG := hG))
    (wp_setCommittedConfiguration :
      github_com.hashicorp.raft.Raft.setCommittedConfiguration.spec (GF := GF) (hG := hG))
    (wp_DecodeConfiguration : github_com.hashicorp.raft.DecodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_max : github_com.hashicorp.raft.max.spec (GF := GF) (hG := hG))
    (wp_goFunc : github_com.hashicorp.raft.raftState.goFunc.spec (GF := GF) (hG := hG))
    (wp_run : github_com.hashicorp.raft.Raft.run.spec (GF := GF) (hG := hG))
    (wp_runFSM : github_com.hashicorp.raft.Raft.runFSM.spec (GF := GF) (hG := hG))
    (wp_runSnapshots : github_com.hashicorp.raft.Raft.runSnapshots.spec (GF := GF) (hG := hG))
    (wp_processHeartbeat : github_com.hashicorp.raft.Raft.processHeartbeat.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.NewRaft.spec (GF := GF) (hG := hG) := by
  intro htb cp c fsmI logsI stableI snapsI transI rpcCh γ i rc eof X tid
  wp_start as ⟨Hcp, %Hcfg, #Hfsm, %Hnb, #Hlogs, %Hnmono, #Hstable, #Hsnaps, #Heof, #Htrans, %Hpv,
    #Hinv, #Hvoter, #Hdi, Hsv, HstV, HtermV, HcidxV, Happ', Happ, Hcomp, Hpend, Hpw, Hboot, %Hrec, #Hfirst, %Hg,
    HfsmOwn, Htok⟩
  obtain ⟨Hcv, ss, Hss, Hgss⟩ := Hg
  obtain ⟨htp, hci, hpend, hcl, hhi1, hhi2, habove, hdplat, hpref, hstg⟩ := Hrec
  ihave #Hglob := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hglob with ⟨⟨%errf, #Herrs⟩, ⟨%kCT, #HkCT, #HkCTs⟩, ⟨%kLVT, #HkLVT, #HkLVTs⟩,
    ⟨%kLVC, #HkLVC, #HkLVCs⟩, #HobsId⟩
  ihave #HstableC := Hstable
  iunfold isStableStore at Hstable
  icases Hstable with ⟨#HGetU, #HSetU, #HGet, #HSet⟩
  ihave #HlogsC := Hlogs
  iunfold isLogStore at Hlogs
  icases Hlogs with ⟨#HLastIdx, #HFirstIdx, #HGetLog, #HStoreLogs, #HStoreLog, #HDelRange, -⟩
  wp_auto
  wp_apply wp_ValidateConfig $$ [$Hcp] as Hcp
  · ipureintro; exact Hcfg
  -- the current term: the crash state's (no term step pending)
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HGetU $$ HkCTs Htok
  iapply (bootRead_S γ rc i X.A X.lat X.s X.tp X.dp X.D X.A.staged)
  iframe #
  iframe Hsv HstV
  isplitl [Hboot]
  · unfold bootV; iexact Hboot
  iintro Hboot Hsv HstV %X1 %HX1 Htok
  obtain ⟨-, -, hs1, htp1, -, hD1, -, hp1⟩ := HX1
  have htd : termDurOk X1.D X1.s X1.tp := hp1.2.2.2.1
  rw [hD1] at htd ⊢
  rw [hs1, htp1, htp] at htd
  have hct : uint.nat ((X.D.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0)) = X.s.term := by
    rcases htd with ⟨-, h⟩ | ⟨t, h, -⟩ | ⟨h, -⟩ <;> first | exact h | cases h
  generalize hctv : (X.D.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0) = ct at hct
  wp_auto
  -- LastIndex: the largest stored index
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HLastIdx $$ Htok
  iapply (bootRead_L γ rc i X.A X.lat X.s X.tp X.dp X.D X.A.staged)
  iframe #
  iframe Hsv HstV Hboot
  iintro Hboot Hsv HstV %X2 %HX2 Htok
  obtain ⟨hA2, hlat2, hs2, -, hdp2, hD2, -, hp2⟩ := HX2
  rw [hA2]
  wp_auto
  ipersist logs
  -- the last entry stored (none if the store is empty)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ bootV rc X.A X.lat ∗ srvVP rc X.s X.tp X.dp ∗
      stVS rc X.D X.A.staged ∗ rtok tid ∗ (∃ e : GoInterface, err_ptr ↦ e) ∗ ∃ lv : Log, lastLog_ptr ↦ lv ∗
      ⌜lv.Index' = X.A.hi ∧ (X.A.hi = W64 0 → lv.Term' = W64 0) ∧
        (X.A.hi ≠ W64 0 → ∃ e, X.A.m.lookup (uint.nat X.A.hi) = some e ∧ uint.nat lv.Term' = e.term)⌝)))
    $$ [Hboot Hsv HstV Htok lastLog err lastIndex] [-]
  · wp_if_destruct
    · have hne : X.A.hi ≠ W64 0 := by intro h; rw [h] at Hif; simp at Hif
      obtain ⟨e, he⟩ : ∃ e, X.A.m.lookup (uint.nat X.A.hi) = some e := by
        rcases hhi2 with h | h
        · exact absurd h hne
        · exact h
      try wp_auto
      wp_bind (App (App (Val #(methods _ _ _)) _) _)
      iapply HGetLog $$ lastLog Htok
      iapply (bootRead_L γ rc i X.A X.lat X.s X.tp X.dp X.D X.A.staged)
      iframe #
      iframe Hsv HstV Hboot
      iintro Hboot Hsv HstV %X3 %HX3 %err' Hpost Htok
      obtain ⟨hA3, -⟩ := HX3
      rw [hA3] at *
      unfold getLogPost
      rw [he]
      icases Hpost with ⟨%Herr, %lv, lastLog, #HlvIs⟩
      subst Herr
      wp_auto
      unfold logIs
      icases HlvIs with ⟨%h, -⟩
      isplitr; · ipureintro; trivial
      iframe
      ipureintro
      refine ⟨by apply BitVec.eq_of_toNat_eq; simpa using h.1, fun h' => absurd h' hne, fun _ => ⟨e, rfl, h.2.1⟩⟩
    · isplitr; · ipureintro; trivial
      iframe
      ipureintro
      have h0 : X.A.hi = W64 0 := by
        apply BitVec.eq_of_toNat_eq
        have : ¬ (uint.Z (W64 0) < uint.Z X.A.hi) := Hif
        simp at this ⊢; word
      exact ⟨h0.symm, fun _ => rfl, fun h => absurd h0 h⟩
  iintro %v ⟨%hv, Hboot, Hsv, HstV, Htok, ⟨%e0, err⟩, %lv, lastLog, %HlvIdx⟩
  subst hv
  wp_auto
  ihave #HtransC := Htrans
  unfold isTransport
  icases Htrans with ⟨#HrpcCh, #HConsumer, #HLocalAddr, #HEncPeer, #HDecPeer, #HSetHB, #HAEP,
    #HAE, #HRV, #HPV, #HIS, #HTN⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HLocalAddr
  wp_auto
  obtain ⟨hPV, hLID, hi, hNC, hBA, hPVD, hSkip, hRCL, hNSR, hMA1, hMA2, hHB1, hHB2, hCT,
    hSI, hLL1, hLL2, hET, hHT, hCT2, hSI2⟩ := Hcfg
  rw [hPV]
  wp_auto
  wp_apply (chan.wp_make1 (V := Loc)) as %applyCh %γapply ⟨#HapplyCh, %HapplyCap, HapplyOwn⟩
  rw [hBA]
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 128)) as %fsmCh %γfsm ⟨#HfsmCh, %HfsmCap, HfsmOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make1 (V := Loc)) as %snapCh %γsnap ⟨#HsnapCh, %HsnapCap, HsnapOwn⟩
  wp_apply (chan.wp_make2 (V := Bool) (W64 1)) as %leaderCh %γlch ⟨#HlchCh, %HlchCap, HlchOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make1 (V := Loc)) as %ccCh %γcc ⟨#HccCh, %HccCap, HccOwn⟩
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HConsumer
  wp_auto
  wp_apply (chan.wp_make1 (V := Loc)) as %usCh %γus ⟨#HusCh, %HusCap, HusOwn⟩
  wp_apply (chan.wp_make1 (V := Loc)) as %urCh %γur ⟨#HurCh, %HurCap, HurOwn⟩
  wp_apply (chan.wp_make1 (V := Unit)) as %sdCh %γsd ⟨#HsdCh, %HsdCap, HsdOwn⟩
  wp_apply (chan.wp_make2 (V := Loc) (W64 64)) as %vCh %γv ⟨#HvCh, %HvCap, HvOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Loc) (W64 8)) as %cfgsCh %γcfgs ⟨#HcfgsCh, %HcfgsCap, HcfgsOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make1 (V := Loc)) as %bsCh %γbs ⟨#HbsCh, %HbsCap, HbsOwn⟩
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %obsM HobsM
  wp_apply (chan.wp_make2 (V := Loc) (W64 1)) as %ltCh %γlt ⟨#HltCh, %HltCap, HltOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Unit) (W64 1)) as %lnCh %γln ⟨#HlnCh, %HlnCap, HlnOwn⟩
  · ipureintro; decide
  wp_apply (chan.wp_make2 (V := Unit) (W64 1)) as %fnCh %γfn ⟨#HfnCh, %HfnCap, HfnOwn⟩
  · ipureintro; decide
  rw [hPVD, Hpv]
  wp_auto
  irename «$r0» => Hr
  generalize «$r0_ptr» = r at *
  iStructNamed Hr
  -- r.conf.Store(*conf)
  ihave Hconfv := (sync.atomic.ownValue_zero (GF := GF) _ (DFrac.own 1)).mp $$ conf
  wp_apply (sync.atomic.Value.wp_Store _ _ (by simp [interface.mkOk]))
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iframe Hconfv
  isplitr
  · ipureintro; trivial
  iintro Hconfv
  imod Hclose with _
  imodintro
  wp_auto
  -- the leaderLock (needed by setState's setLeader)
  have hb : threadBound GF ≤ 2 ^ 28 := htb.threadBound_le
  imod sync.rwmutex.init_RWMutex (E := ⊤) (nroot.@"rw") (r.[Raft, go!"leaderLock"]) $$ leaderLock
    with ⟨%γLL, #HllIs, HllSt, HllToks⟩
  irename currentTerm => HcurTerm
  iStructNamed raftState
  irename currentTerm => FcurrentTerm
  irename commitIndex => FcommitIndex
  irename lastApplied => FlastApplied
  irename state => Fstate
  -- r.setState(Follower), inlined
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setState")]
  wp_call
  unfold Follower
  wp_auto
  wp_apply wp_setLeader_init $$ [$HllIs $HllSt $leaderAddr $leaderID] as ⟨HllSt, leaderAddr, leaderID⟩
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"getState")]
  wp_call
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"getState")]
  wp_call
  wp_auto
  wp_apply sync.atomic.wp_LoadUint32
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists _
  iframe Fstate
  iintro Fstate
  imod Hclose with _
  imodintro
  wp_auto
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"setState")]
  wp_call
  wp_auto
  wp_apply sync.atomic.wp_StoreUint32
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists _
  iframe Fstate
  iintro Fstate
  imod Hclose with _
  imodintro
  wp_auto
  -- r.setCurrentTerm(currentTerm), inlined: the stored term rewritten (an idempotent write), then the atomic
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setCurrentTerm")]
  wp_call
  wp_auto
  iunfold stVS at HstV
  ihave ⟨HstV, HstQ⟩ := (ghostVar_split_half rc.dur.st (1 : Qp).half _).1 $$ HstV
  ihave ⟨Hpw, HpwQ⟩ := (ghostVar_split_half rc.dur.pw 1 _).1 $$ Hpw
  wp_bind (App (App (Val #(methods _ _ _)) _) _)
  iapply HSetU $$ HkCTs [HstQ HpwQ]
  · unfold stWin; iright; iright
    iexists _, ct, X.D, X.A.staged
    unfold stVq
    iframe
    ipureintro; exact ⟨rfl, hctv⟩
  iintro HW
  unfold stWin
  icases HW with (⟨%s', %p', -, Hwr⟩ | ⟨%vb, %Hvb⟩ | ⟨%kb, %v, %D2, %g2, -, HstQ, HpwQ⟩)
  · unfold winRes
    icases Hwr with ⟨HpwQ, -⟩
    icombine Hpw HpwQ gives %Hag
    cases Hag.2
  · cases Hvb
  unfold stVq
  icombine HstV HstQ gives %Hag
  obtain ⟨-, Hag⟩ := Hag
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  icombine HstV HstQ as HstV
  icombine Hpw HpwQ as Hpw
  iapply (bootRewrite_S γ rc i X.A X.lat X.s X.tp X.dp X.D X.A.staged _ ct hctv)
  iframe #
  iframe Hboot Hsv
  isplitl [HstV]
  · unfold stVS; iexact HstV
  iintro Hboot Hsv HstV
  wp_auto
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"setCurrentTerm")]
  wp_call
  wp_auto
  wp_apply sync.atomic.wp_StoreUint64
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists _
  iframe FcurrentTerm
  iintro FcurrentTerm
  imod Hclose with _
  imodintro
  wp_auto
  -- the raft-local ghost state and the FSM channel
  imod ghostVar_alloc (W32 0) with ⟨%γst, Hgst⟩
  icases (ghostVar_split_half γst 1 (W32 0)).mp $$ Hgst with ⟨Hgst, Hgst'⟩
  imod ghostVar_alloc ((0, 0) : Nat × Nat) with ⟨%γll, Hgll⟩
  icases (ghostVar_split_half γll 1 ((0, 0) : Nat × Nat)).mp $$ Hgll with ⟨Hgll, Hgll'⟩
  imod dghostVar_alloc (some ((W64 0, W64 0, W64 0, W64 0) : w64 × w64 × w64 × w64)) with ⟨%γllb, Hllb⟩
  icases dghostVar_halves' γllb _ $$ Hllb with ⟨Hllb, Hllb'⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Nat) with ⟨%γb, Hgb⟩
  imod ghost_map_alloc_empty (K := Loc × SID) (V := Unit) with ⟨%γvtok, Hvtok⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Nat × Snap) with ⟨%γvreg, Hvreg⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) with ⟨%γvlive, Hvlive⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) with ⟨%γvnm, Hvnm⟩
  icases (ghostMapAuth_halves γvnm (∅ : GMap Loc Unit)).mp $$ Hvnm with ⟨Hvnm, Hvnm'⟩
  let rc0 : RCtx GF := { rc with names := ⟨γst, γll, γllb, ⟨γfsm, γst, γst⟩, γb, γvtok, γvreg, γvlive, γvnm⟩ }
  imod start_spsc fsmCh (fsmP γ rc0 i) (fun _ => iprop(False)) γfsm $$ HfsmCh [HfsmOwn]
    with ⟨%γspsc, #HfsmSpsc, HfsmProd, HfsmCons⟩
  · iright; iexact HfsmOwn
  let rc' : RCtx GF := { rc with names := ⟨γst, γll, γllb, γspsc, γb, γvtok, γvreg, γvlive, γvnm⟩ }
  have hfsmP : fsmP γ rc0 i = fsmP γ rc' i := rfl
  rw [hfsmP] at *
  -- lastLock, its fields pinned by NewRaft (`llb`)
  imod sync.init_Mutex (lastLockInv r γ rc' i) ⊤ _ $$ lastLock [lastLogIndex lastLogTerm lastSnapshotIndex
    lastSnapshotTerm Hgll' Hllb'] with #HlastLock
  · inext; unfold lastLockInv
    rw [show (zeroValDef : raftState).lastLogIndex' = W64 0 from rfl,
      show (zeroValDef : raftState).lastLogTerm' = W64 0 from rfl,
      show (zeroValDef : raftState).lastSnapshotIndex' = W64 0 from rfl,
      show (zeroValDef : raftState).lastSnapshotTerm' = W64 0 from rfl]
    iexists _, _, _, _
    iframe lastLogIndex lastLogTerm lastSnapshotIndex lastSnapshotTerm
    isplitl [Hgll']
    · rw [show uint.nat (W64 0) = 0 from rfl]; iexact Hgll'
    isplitr
    · ileft; ipureintro; rfl
    iright; iexact Hllb'
  -- r.setLastLog(lastLog.Index, lastLog.Term), inlined (the fields pinned)
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setLastLog")]
  wp_call
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"setLastLog")]
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HlastLock] as ⟨Hlocked, HR⟩
  iunfold lastLockInv at HR
  icases HR with ⟨%li0, %lt0, %si0, %st0, HlI, HlT, HsI, HsT, Hgll', #Hsn, Hb⟩
  icases Hb with (Hb | Hb)
  · icombine Hb Hllb gives %Hag; cases Hag.2
  icombine Hb Hllb gives %Hag
  obtain ⟨-, Hag⟩ := Hag
  simp only [Option.some.injEq, Prod.mk.injEq] at Hag
  obtain ⟨h1, h2, h3, h4⟩ := Hag
  subst li0 lt0 si0 st0
  wp_auto
  imod ghostVar_update_halves (uint.nat lv.Index', uint.nat lv.Term') γll _ _ $$ Hgll Hgll' with ⟨Hgll, Hgll'⟩
  imod dghostVar_update_halves (some (lv.Index', lv.Term', W64 0, W64 0)) _ _ _ $$ Hb Hllb with ⟨Hb, Hllb⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$HlastLock $Hlocked HlI HlT HsI HsT Hgll' Hb]
  · inext; unfold lastLockInv
    iexists _, _, _, _
    iframe HlI HlT HsI HsT
    isplitl [Hgll']
    · iexact Hgll'
    isplitr
    · ileft; ipureintro; rfl
    iright; iexact Hb
  -- the lastApplied cell (at 0)
  imod inv_alloc appliedN ⊤ iprop(∃ a : w64,
      r.[Raft, go!"raftState"].[raftState, go!"lastApplied"] ↦ a ∗
      monoNatAuthOwn rc'.dur.applied (1 : Qp).half (uint.nat a))
    $$ [FlastApplied Happ'] with #HappliedCell
  · inext; iexists _; iframe FlastApplied
    rw [show uint.nat (zeroValDef : raftState).lastApplied' = 0 from rfl]; iexact Happ'
  -- restore the latest snapshot
  imod (sync.atomic.ownValue_dfractional (GF := GF) _ _).dfractional_persist (DFrac.own 1) $$ Hconfv
    with #Hconfv
  ipersist snapshots
  ipersist fsm
  ihave Hlp0 := ownPointer_zero_cfg _ $$ latestConfiguration
  ihave Hboot : (bootV rc' X.A X.lat : IProp GF) $$ [Hboot]
  · unfold bootV; iexact Hboot
  have hdur : rc'.dur = rc.dur := rfl
  ihave Hsv : (srvVP rc' X.s X.tp X.dp : IProp GF) $$ [Hsv]
  · unfold srvVP; rw [hdur]; iexact Hsv
  ihave Hpend : (ghostVar rc'.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) : IProp GF) $$ [Hpend]
  · rw [hdur]; iexact Hpend
  ihave Happ : (monoNatAuthOwn rc'.dur.applied (1 : Qp).half 0 ∨ ⌜∃ d, X.dp = some d⌝ : IProp GF) $$ [Happ]
  · rw [hdur]; iexact Happ
  wp_apply (wp_restoreSnapshot r γ i rc' c snapsI fsmI eof X.A X.lat X.s X.tp X.dp lv.Index' lv.Term'
      (zero_val Configuration) (zero_val Configuration) (W64 0) (W64 0) null tid)
    $$ [$Hboot $Hpend $Hsv $Happ $Hllb configurations $Hlp0 $HfsmOwn $Htok]
    as ⟨Hboot, Hpend, Hsv, Htok, #Hlat, Hres⟩
  · iframe #
    isplitr; · ipureintro; exact hNSR
    isplitr; · rw [show snapWin γ rc' i = snapWin γ rc i from rfl]; iexact Hsnaps
    isplitr; · rw [show srvDurInvRaw γ rc' i = srvDurInvRaw γ rc i from rfl]; iexact Hdi
    isplitr; · unfold appliedCell; iexact HappliedCell
    rw [show (zero_val configurations : configurations) = configurations.mk (zero_val Configuration) (W64 0)
      (zero_val Configuration) (W64 0) from rfl]
    iexact configurations
  -- the boot reads' facts of the crash state
  obtain ⟨hlog2, -, hvm2, -, -, ⟨hlod2, -, -⟩, -, -, hdpl2⟩ := hp2
  rw [hA2, hs2] at hlog2
  rw [hD2, hs2] at hvm2
  rw [hdp2] at hlod2
  rw [hdp2, hlat2] at hdpl2
  imod (restore_unify (GF := GF) γ rc' i (E := ⊤) r X.lat X.dp lv.Index' lv.Term') $$ [$Hlat $Hres]
    with ⟨Happ, Hlb, Hllb, ⟨%ccfg0, %cfg0, %cidx0, %li0, %p0, Hcfgs, %Hcb, Hlp, Hpc⟩, Hfsm0⟩
  ihave #Hdi' : (srvDurInvRaw γ rc' i : IProp GF) $$ []
  · rw [show srvDurInvRaw γ rc' i = srvDurInvRaw γ rc i from rfl]; iexact Hdi
  -- the pending discard's facts, the latest's lower bound, gprot's facts of the crash state
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  ihave H1 := bootDpRes (GF := GF) γ rc' i (E := ⊤) (fun _ _ => CoPset.mem_full) X.A X.lat X.s X.tp X.dp
    $$ [$Hdi' $Hboot $Hsv]
  imod H1 $$ Hnc with ⟨Hnc, Hboot, Hsv, #Hdpr, #Hlatlb⟩
  ihave H2 := bootPeek (GF := GF) γ rc' i (E := ⊤) (fun _ _ => CoPset.mem_full) X.A X.lat X.s X.tp X.dp
    iprop(⌜bootF γ X.s X.lat X.dp⌝) $$ [$Hdi' $Hboot $Hsv $Hpend]
  · iintro %X3 %HX3 #Hdl Hown
    rw [HX3.2.2.1]
    iapply (boot_facts (GF := GF) γ rc' i gprotN_durN X.s X.lat X.dp Hcv hdplat) $$ [$Hinv $Hown $Hlat $Hdl $Hdpr]
  imod H2 $$ Hnc with ⟨Hnc, Hboot, Hsv, Hpend, %HF⟩
  iframe Hnc
  imodintro
  -- fix 2: the latest snapshot
  wp_bind (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastSnapshot")) (Val #()))
  iapply (getLastSnapshot_pinned (GF := GF) γ rc' i r lv.Index' lv.Term' (latIdxW X.lat) (latTermW X.lat))
  iframe Hllb
  iframe #
  iintro Hllb
  wp_auto
  -- the main goroutine's views, over rc'
  generalize hDg : ({ ints := X.D.ints.insert (go!"CurrentTerm" : List w8) ct, bytes := X.D.bytes } : StableAbs) = D'
    at *
  have hvmD : voteMatches D' X.s := by
    rw [← hDg]; unfold voteMatches
    rw [GMap.lookup_insert_ne _ _ (by decide)]; exact hvm2
  ihave Hpw : (ghostVar rc'.dur.pw 1 (none : Option Pend) : IProp GF) $$ [Hpw]
  · rw [hdur]; iexact Hpw
  ihave HstV : (stVS rc' D' X.A.staged : IProp GF) $$ [HstV]
  · unfold stVS; rw [hdur]; iexact HstV
  ihave Hcomp : (monoNatAuthOwn rc'.dur.comp (1 : Qp).half X.c : IProp GF) $$ [Hcomp]
  · rw [hdur]; iexact Hcomp
  ihave Hgll : (ghostVar rc'.names.lastLog (1 : Qp).half (uint.nat lv.Index', uint.nat lv.Term') : IProp GF) $$ [Hgll]
  · iexact Hgll
  obtain ⟨hlen0, hdl0, hents0, hdpd0, hdpn0⟩ := HF
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      fixPost (GF := GF) rc' false X.lat D' X.A.staged X.s.term lastLog_ptr ∗ rtok tid ∗ r_ptr ↦ r)))
    $$ [Hboot Hsv Hpend Hpw HstV Hcomp Happ Hllb Hgll lastLog Htok r snapIdx snapTerm] [-]
  · rw [htp]
    rcases hL : X.lat with _ | ⟨m, b⟩
    · -- no snapshot: nothing to discard
      have hdpN : X.dp = none := by
        rcases hd : X.dp with _ | d
        · rfl
        · obtain ⟨m, b, h, -⟩ := hdpl2 d hd; rw [hL] at h; cases h
      rw [hdpN]
      simp only [latIdxW, latTermW]
      wp_if_destruct
      · exfalso; simp at Hif
      icases Happ with (Happ | %hd)
      rotate_left
      · obtain ⟨d, hd⟩ := hd; cases hd
      isplitr; · ipureintro; trivial
      iframe Htok r
      unfold fixPost
      simp only [latIdxW, latTermW, latIdx]
      iexists X.s, X.A, lv, X.c
      iframe
      ipureintro
      have habove' := habove
      rw [hL] at habove' hcl
      obtain ⟨h1, h2⟩ := lastLog_of_hi X.A X.s.log 0 lv hlog2.1 hhi1 hhi2 habove' HlvIdx (Nat.zero_le _)
      simp only [latIdx] at hcl habove'
      exact ⟨rfl, hci, hvmD, hstg, Nat.zero_le _, hcl, habove', Or.inl ⟨h1, h2, Nat.zero_le _⟩⟩
    · simp only [latIdxW, latTermW]
      iunfold latFacts at Hlat
      icases Hlat with ⟨-, ⟨%e, #HCe, %He⟩, -, -, -⟩
      wp_if_destruct
      rotate_left
      · exfalso; apply Hif; have := He.2; word
      icases Hfirst with (%hn | #HFI)
      · cases hn
      iunfold isLogStoreFirst at HFI
      simp only [Hif, decide_true]
      wp_auto
      have habove' := habove
      rw [hL] at habove' hcl hdplat hpref hdpn0
      simp only [latIdx, latTerm] at habove' hcl hdplat hpref hdpn0 hdpd0
      rw [show rc.ownL = rc'.ownL from rfl]
      rcases hdp : X.dp with _ | d
      · -- no discard pending: the store holds the snapshot's entry, or nothing at or below it
        obtain ⟨hxd, hex⟩ := hdpn0 hdp
        obtain ⟨e', he', he't⟩ := hex (by simp)
        wp_bind (App (Val #(methods _ _ _)) _)
        iapply HFI $$ Htok
        iapply (bootRead_L (GF := GF) γ rc' i X.A (some (m, b)) X.s none none D' X.A.staged)
        iframe #
        iframe Hsv HstV Hboot
        iintro Hboot Hsv HstV %X4 %HX4 %r0 %Hr0 Htok
        rw [HX4.1] at Hr0
        wp_auto
        rcases Hr0 with ⟨hr0, hA0⟩ | ⟨hr0s, hr0m⟩
        · -- an empty store: the log is the snapshot's prefix (nothing above it stored)
          wp_if_destruct
          · exfalso; word
          try simp only [Hif, decide_false]
          try wp_auto
          isplitr; · ipureintro; trivial
          iframe Htok r
          unfold fixPost
          simp only [latIdxW, latTermW, latIdx, latTerm]
          iexists X.s, X.A, lv, X.c
          icases Happ with (Happ | %hd)
          rotate_left
          · obtain ⟨d, hd⟩ := hd; cases hd
          iframe
          ipureintro
          have hhi0 : X.A.hi = W64 0 := by
            rcases hhi2 with h | ⟨e2, h⟩
            · exact h
            · rw [hA0] at h; simp at h
          have hlx : X.s.log.length = uint.nat m.Index' := by
            have h1 := (proto.ent_le_length he').2
            rcases Nat.lt_or_ge (uint.nat m.Index') X.s.log.length with hlt | hge'
            · have h2 := habove' X.s.log.length hlt (Nat.le_refl _)
              obtain ⟨e3, he3⟩ := proto.ent_isSome X.s.log X.s.log.length (by omega) (Nat.le_refl _)
              rw [he3, hA0] at h2; simp at h2
            · omega
          refine ⟨rfl, hci, hvmD, hstg, hxd, hcl, habove', Or.inr ⟨by trivial, ?_, hlx, ?_⟩⟩
          · rw [HlvIdx.1, hhi0]; have := He.2; simp; omega
          · unfold lastTerm; rw [hlx, proto.termAt_of_ent he', he't]
        · -- a store with a smallest key `r0`
          obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hr0s
          have hr0pos : 0 < uint.nat r0 := (proto.ent_le_length (hlog2.1 _ _ he0)).1
          have hge : uint.nat m.Index' ≤ uint.nat X.A.hi := by
            by_cases hle : uint.nat r0 ≤ uint.nat m.Index'
            · obtain ⟨e2, he2⟩ := hpref hdp _ _ he0 hle
              exact hhi1 _ _ he2
            · have := hhi1 _ _ he0; omega
          obtain ⟨hlI, hlT⟩ := lastLog_of_hi X.A X.s.log _ lv hlog2.1 hhi1 hhi2 habove' HlvIdx hge
          wp_if_destruct
          rotate_left
          · exfalso; apply Hif; word
          try simp only [Hif, decide_true]
          try wp_auto
          wp_if_destruct
          · -- the store holds the snapshot's entry, of the snapshot's term: kept
            obtain ⟨e2, he2⟩ := hpref hdp _ _ he0 (by word)
            have he2' : e2 = e' := by have := hlog2.1 _ _ he2; rw [he'] at this; cases this; rfl
            subst he2'
            wp_bind (App (App (Val #(methods _ _ _)) _) _)
            iapply HGetLog $$ «at» Htok
            iapply (bootRead_L (GF := GF) γ rc' i X.A (some (m, b)) X.s none none D' X.A.staged)
            iframe #
            iframe Hsv HstV Hboot
            iintro Hboot Hsv HstV %X5 %HX5 %err' Hpost Htok
            rw [HX5.1]
            unfold getLogPost
            rw [he2]
            icases Hpost with ⟨%Herr, %lva, Hat, #Hlva⟩
            subst Herr
            unfold logIs
            icases Hlva with ⟨%hlva, -⟩
            have hTa : lva.Term' = m.Term' := by
              apply BitVec.eq_of_toNat_eq
              have := hlva.2.1; rw [he't] at this; simpa using this
            wp_auto
            wp_if_destruct
            all_goals try (exfalso; simp [hTa] at Hif; done)
            isplitr; · ipureintro; trivial
            iframe Htok r
            unfold fixPost
            simp only [latIdxW, latTermW, latIdx, latTerm]
            iexists X.s, X.A, lv, X.c
            icases Happ with (Happ | %hd)
            rotate_left
            · obtain ⟨d, hd⟩ := hd; cases hd
            iframe
            ipureintro
            refine ⟨rfl, hci, hvmD, hstg, hxd, hcl, habove', Or.inl ⟨hlI, hlT, ?_⟩⟩
            rw [HlvIdx.1]; exact hge
          · try simp only [Hif, decide_false]
            try wp_auto
            isplitr; · ipureintro; trivial
            iframe Htok r
            unfold fixPost
            simp only [latIdxW, latTermW, latIdx, latTerm]
            iexists X.s, X.A, lv, X.c
            icases Happ with (Happ | %hd)
            rotate_left
            · obtain ⟨d, hd⟩ := hd; cases hd
            iframe
            ipureintro
            refine ⟨rfl, hci, hvmD, hstg, hxd, hcl, habove', Or.inl ⟨hlI, hlT, ?_⟩⟩
            rw [HlvIdx.1]; exact hge
      · sorry
  iintro %v ⟨%hv, Hfix, Htok, r⟩
  subst hv
  wp_auto
  -- fix 4: lastLog raised to the snapshot's last entry when below
  iunfold fixPost at Hfix
  icases Hfix with ⟨%s1, %A1, %lv1, %c1, Hboot, Hsv, Hpend, Hpw, HstV, Hcomp, Happ, Hllb, Hgll, lastLog, %Hf1⟩
  wp_bind (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"getLastSnapshot")) (Val #()))
  iapply (getLastSnapshot_pinned (GF := GF) γ rc' i r lv1.Index' lv1.Term' (latIdxW X.lat) (latTermW X.lat))
  iframe Hllb
  iframe #
  iintro Hllb
  wp_auto
  obtain ⟨ht1, hci1, hvm1, hg1, hx1, hc1, hab1, hl1⟩ := Hf1
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      fixPost (GF := GF) rc' true X.lat D' X.A.staged X.s.term lastLog_ptr ∗ r_ptr ↦ r)))
    $$ [Hboot Hsv Hpend Hpw HstV Hcomp Happ Hllb Hgll lastLog r snapIdx snapTerm] [-]
  · wp_if_destruct
    · -- below: the log is the snapshot's prefix
      have hl2 : uint.nat lv1.Index' < latIdx X.lat ∧ s1.log.length = latIdx X.lat ∧
          lastTerm s1.log = latTerm X.lat := by
        rcases hl1 with ⟨-, -, h⟩ | ⟨-, h⟩
        · exfalso; rw [← latIdxW_nat] at h; word
        · exact h
      try wp_auto
      wp_bind (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastLog")) _) _)
      iapply (setLastLog_pinned (GF := GF) γ rc' i r lv1.Index' lv1.Term' (latIdxW X.lat) (latTermW X.lat)
        (latIdxW X.lat) (latTermW X.lat))
      iframe Hllb Hgll
      iframe #
      iintro Hllb Hgll
      wp_auto
      isplitr; · ipureintro; trivial
      iframe r
      unfold fixPost
      iexists s1, A1, _, c1
      iframe lastLog
      simp only
      iframe
      ipureintro
      refine ⟨ht1, hci1, hvm1, hg1, hx1, hc1, hab1, Or.inl ⟨?_, ?_, ?_⟩⟩ <;>
        simp only [latIdxW_nat, latTermW_nat] <;> omega
    · try wp_auto
      isplitr; · ipureintro; trivial
      iframe r
      unfold fixPost
      iexists s1, A1, lv1, c1
      iframe
      ipureintro
      refine ⟨ht1, hci1, hvm1, hg1, hx1, hc1, hab1, Or.inl ?_⟩
      rcases hl1 with h | ⟨-, h, -⟩
      · exact h
      · exfalso; rw [← latIdxW_nat] at h; word
  iintro %v ⟨%hv, Hfix, r⟩
  subst hv
  wp_auto
  -- restoreFromCommittedLogs (`RestoreCommittedLogs = false`: nothing)
  rw [hRCL]
  ipersist RestoreCommittedLogs
  wp_apply wp_restoreFromCommittedLogs $$ [$RestoreCommittedLogs]
  sorry
