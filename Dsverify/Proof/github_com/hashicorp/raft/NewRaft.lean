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
    #Hinv, #Hvoter, #Hdi, Hsv, HstV, HtermV, HcidxV, Happ, Hcomp, Hpend, Hpw, Hboot, %Hrec, #Hfirst, %Hg,
    HfsmOwn, Htok⟩
  obtain ⟨Hcv, ss, Hss, Hgss⟩ := Hg
  obtain ⟨htp, hci, hpend, hcl, hhi1, hhi2, habove, hdplat, hpref⟩ := Hrec
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
  obtain ⟨hA2, -⟩ := HX2
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
  sorry
