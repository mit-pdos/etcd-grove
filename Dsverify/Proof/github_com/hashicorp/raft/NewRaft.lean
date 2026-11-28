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

instance observersP_fractional (γ : GNames) (i : SID) (r : Loc) :
    Fractional (observersP (GF := GF) γ i r) := by
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

/-- (stage 3) A fresh snapshot store's invariant: nothing stored, no install pending. -/
theorem snapCell_alloc (rc : github_com.hashicorp.raft.RCtx GF) (γ : github_com.hashicorp.raft.gprot.GNames)
    (i : github_com.hashicorp.raft.proto.SID) :
    rc.ownSS none ∗ ghostVar rc.names.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ⊢
      |={⊤}=> github_com.hashicorp.raft.snapCell rc γ i := by
  iintro ⟨H1, H2⟩
  unfold github_com.hashicorp.raft.snapCell
  iapply inv_alloc
  inext
  iexists none, none
  iframe
  isplitr
  · unfold github_com.hashicorp.raft.latestOk; itrivial
  ileft; ipureintro; rfl

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
  intro htb cp c fsmI logsI stableI snapsI transI rpcCh γ i ownL ownS ownSS eof snapP fsmOwn respP
    sst tid
  wp_start as ⟨Hcp, %Hcfg, #Hfsm, %Hnb, #Hlogs, %Hnmono, #Hstable, #Hsnaps, #Heof, #Htrans, %Hpv,
    HownL, HownS, HownSS, %Hsst, #Hinv, #Hvoter, Hsrv, Hterm, Hlogc, Hcidx, Hdur, %Hg, HfsmOwn, Htok⟩
  obtain ⟨Hcv, ss, Hss, Hgss⟩ := Hg
  -- (stage 4) the server's initial state: a bootstrap voter's (log `[g]`, term 1) or a non-member's
  have hgk : γ.g.kind = kConfig := by rw [Hgss]; rfl
  have hgt : γ.g.term = 1 := by rw [Hgss]; rfl
  have hshape : ((initSrv γ.cv γ.g i).log = [] ∧ (initSrv γ.cv γ.g i).term = 0 ∧
        i ∉ γ.cv γ.g.data) ∨
      ((initSrv γ.cv γ.g i).log = [γ.g] ∧ (initSrv γ.cv γ.g i).term = 1 ∧ i ∈ γ.cv γ.g.data) := by
    by_cases hm : i ∈ γ.cv γ.g.data
    · right; unfold initSrv; simp [hm]
    · left; unfold initSrv; simp [hm]
  have hs0 : initSrv γ.cv γ.g i =
      SState.mk (initSrv γ.cv γ.g i).term (initSrv γ.cv γ.g i).log 0 [] (0, 0) 0 := by
    unfold initSrv; split <;> rfl
  generalize hL0 : (initSrv γ.cv γ.g i).log = L0 at hshape hs0 ⊢
  generalize ht0 : (initSrv γ.cv γ.g i).term = t0 at hshape hs0 ⊢
  rw [hs0]
  have hct : (sst.ints.lookup (go!"CurrentTerm" : List w8)).getD (W64 0) = W64 (t0 : Int) := by
    rw [Hsst.1]
    rcases hshape with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · rw [if_neg h2, h1]; rfl
    · rw [if_pos h2, h1]; rfl
  have hhi : (LogAbs.empty.store 1 L0).hi = W64 (L0.length : Int) := by
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h
    · rfl
    · rw [genesisStore_hi]; rfl
  have hstore : ∀ k, (LogAbs.empty.store 1 L0).m.lookup k = ent L0 k := by
    intro k
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h
    · simp [LogAbs.store, LogAbs.empty, LogAbs.ins, ent]
    · rw [genesisStore_m]
      by_cases hk : k = 1
      · subst hk; rfl
      · rw [if_neg hk]; unfold ent; split
        · rfl
        · rename_i hk0; simp; omega
  have hlast0 : (L0.length, lastTerm L0) = ((0 : Nat), (0 : Nat)) ∨ L0 = [γ.g] := by
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h
    · left; rfl
    · right; rfl
  ihave #Hglob := pkgGlobals_access $$ Hpkg
  unfold pkgGlobals
  icases Hglob with ⟨⟨%errf, #Herrs⟩, ⟨%kCT, #HkCT, #HkCTs⟩, ⟨%kLVT, #HkLVT, #HkLVTs⟩,
    ⟨%kLVC, #HkLVC, #HkLVCs⟩, #HobsId⟩
  ihave #HstableC := Hstable
  unfold isStableStore
  icases Hstable with ⟨#HGetU, #HSetU, #HGet, #HSet⟩
  ihave #HlogsC := Hlogs
  unfold isLogStore
  icases Hlogs with ⟨#HLastIdx, #HFirstIdx, #HGetLog, #HStoreLogs, #HStoreLog, #HDelRange⟩
  wp_auto
  wp_apply wp_ValidateConfig $$ [$Hcp] as Hcp
  · ipureintro; exact Hcfg
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HGetU $$ HownS HkCTs Htok
  iintro HownS Htok
  wp_auto
  -- LastIndex: 1
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HLastIdx $$ Htok
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists _
  iframe HownL
  iintro HownL
  imod Hclose with _
  imodintro
  iintro Htok
  rw [hhi]
  wp_auto
  ipersist logs
  irename logs => HlogsLoc
  -- the last entry: the genesis (a bootstrap voter), or none (a non-member)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ownL (LogAbs.empty.store 1 L0) ∗ rtok tid ∗
      (∃ e : GoInterface, err_ptr ↦ e) ∗ ∃ lv : Log, lastLog_ptr ↦ lv ∗
      ⌜uint.nat lv.Index' = L0.length ∧ uint.nat lv.Term' = lastTerm L0⌝)))
    $$ [HownL Htok lastLog err lastIndex] [-]
  · rcases hshape with ⟨hL, -⟩ | ⟨hL, -⟩
    · subst hL
      wp_if_destruct
      · exfalso; simp at Hif
      isplitr; · ipureintro; trivial
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    · subst hL
      wp_if_destruct
      rotate_left
      · exfalso; simp at Hif
      wp_bind (App (App (Val #(methods _ _ _)) _) _)
      iapply HGetLog $$ lastLog Htok
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hclose
      inext
      iexists _
      iframe HownL
      iintro HownL
      imod Hclose with _
      imodintro
      iintro %err' Hpost Htok
      unfold getLogPost
      rw [genesisStore_m, if_pos (by rfl)]
      icases Hpost with ⟨%Herr, %lv, lastLog, #HlvIs⟩
      subst Herr
      wp_auto
      unfold logIs; icases HlvIs with ⟨%h, -⟩
      isplitr; · ipureintro; trivial
      iframe
      ipureintro; exact ⟨h.1, h.2.1⟩
  iintro %v ⟨%hv, HownL, Htok, ⟨%e0, err⟩, %lv, lastLog, %HlvIdx⟩
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
  -- r.setCurrentTerm(1), inlined
  rw [hct]
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setCurrentTerm")]
  wp_call
  wp_auto
  wp_bind (App (App (Val #(methods _ _ _)) _) _)
  iapply HSetU $$ HownS HkCTs
  iintro HownS
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
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γap, Hgap, -⟩
  icases monoNatAuth_halves γap 0 $$ Hgap with ⟨Hgap, Hgap'⟩
  -- (stage 3) the compaction frontier and the pending-install record
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γcomp, Hcomp, #Hcomplb⟩
  imod ghostVar_alloc (none : Option (Nat × Nat × GoString)) with ⟨%γpend, Hpend⟩
  icases (ghostVar_split_half γpend 1 (none : Option (Nat × Nat × GoString))).mp $$ Hpend
    with ⟨Hpend, Hpend'⟩
  imod ghostVar_alloc ((0, 0) : Nat × Nat) with ⟨%γll, Hgll⟩
  icases (ghostVar_split_half γll 1 ((0, 0) : Nat × Nat)).mp $$ Hgll with ⟨Hgll, Hgll'⟩
  imod ghost_map_alloc_empty (K := Nat) (V := Nat) with ⟨%γb, Hgb⟩
  -- (stage 2) the pending appends and the verify futures' registry
  imod ghostVar_alloc ([] : RLog) with ⟨%γlp, Hglp⟩
  icases (ghostVar_split_half γlp 1 ([] : RLog)).mp $$ Hglp with ⟨Hglp, Hglp'⟩
  imod ghost_map_alloc_empty (K := Loc × SID) (V := Unit) with ⟨%γvtok, Hvtok⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Nat × Snap) with ⟨%γvreg, Hvreg⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) with ⟨%γvlive, Hvlive⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) with ⟨%γvnm, Hvnm⟩
  icases (ghostMapAuth_halves γvnm (∅ : GMap Loc Unit)).mp $$ Hvnm with ⟨Hvnm, Hvnm'⟩
  let rc0 : RCtx GF := ⟨ownL, ownSS, snapP, ownS, fsmOwn, respP,
    ⟨γst, γap, γll, ⟨γfsm, γst, γst⟩, γb, γlp, γvtok, γvreg, γvlive, γvnm, γcomp, γpend⟩⟩
  imod start_spsc fsmCh (fsmP γ rc0 i) (fun _ => iprop(False)) γfsm $$ HfsmCh [HfsmOwn]
    with ⟨%γspsc, #HfsmSpsc, HfsmProd, HfsmCons⟩
  · iright; iexact HfsmOwn
  let rc : RCtx GF := ⟨ownL, ownSS, snapP, ownS, fsmOwn, respP,
    ⟨γst, γap, γll, γspsc, γb, γlp, γvtok, γvreg, γvlive, γvnm, γcomp, γpend⟩⟩
  have hfsmP : fsmP γ rc0 i = fsmP γ rc i := rfl
  rw [hfsmP] at *
  -- lastLock
  imod sync.init_Mutex (lastLockInv r γ rc i) ⊤ _ $$ lastLock [lastLogIndex lastLogTerm lastSnapshotIndex
    lastSnapshotTerm Hgll'] with #HlastLock
  · inext; unfold lastLockInv; iexists _, _, _, _; iframe
    isplitl
    rotate_left
    · ileft; ipureintro; rfl
    have h : (uint.nat (zeroValDef : raftState).lastLogIndex',
      uint.nat (zeroValDef : raftState).lastLogTerm') = ((0, 0) : Nat × Nat) := rfl
    rw [h]; iexact Hgll'
  -- r.setLastLog(lastLog.Index, lastLog.Term), inlined
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"setLastLog")]
  wp_call
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"setLastLog")]
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HlastLock] as ⟨Hlocked, HR⟩
  unfold lastLockInv
  icases HR with ⟨%li0, %lt0, %si0, %st0, HlI, HlT, HsI, HsT, Hgll', Hsn⟩
  wp_auto
  icombine Hgll Hgll' gives % ⟨_, Hll⟩
  imod ghostVar_update_halves (uint.nat lv.Index', uint.nat lv.Term') γll _ _ $$ Hgll Hgll'
    with ⟨Hgll, Hgll'⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$HlastLock $Hlocked HlI HlT HsI HsT Hgll' Hsn]
  · iexists _, _, _, _; iframe
  ipersist snapshots
  wp_apply wp_restoreSnapshot $$ [$snapshots $Hsnaps $HownSS $Htok] as ⟨HownSS, Htok⟩
  rw [hRCL]
  ipersist RestoreCommittedLogs
  wp_apply wp_restoreFromCommittedLogs $$ [$RestoreCommittedLogs]
  -- getLastSnapshot, inlined
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"getLastSnapshot")]
  wp_call
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"getLastSnapshot")]
  wp_call
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HlastLock] as ⟨Hlocked, HR⟩
  icases HR with ⟨%li0, %lt0, %si0, %st0, HlI, HlT, HsI, HsT, Hgll', #Hsn⟩
  ihave ⟨Hgap, %Hsi0⟩ : (monoNatAuthOwn γap (1 : Qp).half 0 ∗ ⌜si0 = W64 0⌝ : IProp GF) $$ [Hgap]
  · icases Hsn with (%h | ⟨%e0, -, -, #Hlb0, -⟩)
    · iframe; ipureintro; exact h
    · unfold applLb
      ihave ⟨Hgap, %hle⟩ := monoNatAuth_lb_le γap _ 0 _ $$ [$Hgap $Hlb0]
      iframe; ipureintro; apply BitVec.eq_of_toNat_eq; simp only [uint.nat] at hle; simp; omega
  subst Hsi0
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$HlastLock $Hlocked HlI HlT HsI HsT Hgll' Hsn]
  · iexists _, _, _, _; iframe; inext; iexact Hsn
  -- getLastApplied, inlined
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty) (m := go!"getLastApplied")]
  wp_call
  rw [MethodUnfold.method_unfold (t := go.GoType.PointerType raftState.ty) (m := go!"getLastApplied")]
  wp_call
  wp_auto
  wp_apply sync.atomic.wp_LoadUint64
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  inext
  iexists _
  iframe FlastApplied
  iintro FlastApplied
  imod Hclose with _
  imodintro
  wp_auto
  wp_apply wp_max
  ihave Hlatest := ownPointer_zero_cfg _ $$ latestConfiguration
  ipersist logs
  ihave HI : (∃ idx : w64, "index" ∷ index_ptr ↦ idx ∗ "HownL" ∷ ownL (LogAbs.empty.store 1 L0) ∗ "Htok" ∷ rtok tid ∗
      "Hst" ∷ ((⌜idx = W64 1⌝ ∗ r.[Raft, go!"configurations"] ↦ zero_val configurations ∗
          sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"])
            (DFrac.own 1) null) ∨
       (⌜idx = W64 2 ∧ L0 = [γ.g]⌝ ∗ ∃ cfg cfg' : Configuration,
          r.[Raft, go!"configurations"] ↦
            configurations.mk (zero_val Configuration) (W64 0) cfg (W64 1) ∗
          cfg.Servers' ↦* ss ∗
          (∃ p : Loc, sync.atomic.ownPointer (T' := Configuration)
            (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗ p ↦□ cfg') ∗
          cfg'.Servers' ↦* ss)) : IProp GF) $$ [index HownL Htok configurations Hlatest]
  · iexists _; iframe; ileft; iframe; ipureintro; simp
  repeat (irename : (emp : IProp GF) => Hjunk; iclear Hjunk)
  repeat (irename : ("_" ∷ (True : IProp GF) : IProp GF) => Hjunk; iclear Hjunk)
  irename : ((_ : Loc) ↦ (zero_val Loc : Loc) : IProp GF) => Hres0
  icombine Fstate FlastApplied as Hsafe
  irename : ((_ : Loc) ↦ (W32 0 : w32) : IProp GF) => Hjunk
  iclear Hjunk
  irename : ((_ : Loc) ↦ (W64 0 : w64) : IProp GF) => Hjunk
  iclear Hjunk
  icases Hsafe with ⟨Fstate, FlastApplied⟩
  irename : (trans_ptr ↦ (GoInterface.ok transI : GoInterface) : IProp GF) => Htransl
  wp_for HI
  wp_if_destruct
  · -- the iteration at index 1: the genesis configuration entry
    icases Hst with (⟨%Hidx, Hcfgs, Hlatest⟩ | ⟨⟨%Hidx, -⟩, %cfg, %cfg', Hcfgs, Hss1, Hlatest, Hss2⟩)
    rotate_left
    · exfalso; subst Hidx
      have hif : uint.Z (W64 2) ≤ uint.Z lv.Index' := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hL1 : L0.length ≤ 1 := by rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ <;> subst h <;> simp
      have := HlvIdx.1
      word
    subst Hidx
    have hL : L0 = [γ.g] := by
      rcases hshape with ⟨h, -⟩ | ⟨h, -⟩
      · subst h; exfalso
        have hif : uint.Z (W64 1) ≤ uint.Z lv.Index' := by
          first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
        have := HlvIdx.1
        simp only [List.length_nil] at this; word
      · exact h
    subst hL
    wp_bind (App (App (Val #(methods _ _ _)) _) _)
    iapply HGetLog $$ entry Htok
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose
    inext
    iexists _
    iframe HownL
    iintro HownL
    imod Hclose with -
    imodintro
    iintro %err Hpost Htok
    unfold getLogPost
    rw [genesisStore_m, if_pos (by rfl)]
    icases Hpost with ⟨%Herr, %lv1, entry, #Hlv1⟩
    subst Herr
    wp_auto
    unfold logIs
    icases Hlv1 with ⟨%Hlv1, #Hdata, #Hext⟩
    obtain ⟨Hlv1i, -, Hlv1t⟩ := Hlv1
    have hgd : γ.g.data = encodeServers ss := by rw [Hgss]; rfl
    rw [hgk] at Hlv1t
    rw [hgd]
    have htype : lv1.Type' = W8 5 := by
      unfold kConfig at Hlv1t; apply BitVec.eq_of_toNat_eq; simpa using Hlv1t
    rw [MethodUnfold.method_unfold (t := go.GoType.PointerType Raft.ty)
      (m := go!"processConfigurationLogEntry")]
    wp_call
    wp_auto
    rw [htype]
    wp_auto
    rw [show (zero_val configurations : configurations) = configurations.mk (zero_val Configuration)
      (W64 0) (zero_val Configuration) (W64 0) from rfl]
    wp_apply wp_setCommittedConfiguration $$ [$Hcfgs] as Hcfgs
    wp_apply wp_DecodeConfiguration $$ [$Hdata] as %cfg ⟨-, Hss1⟩
    have hslc := wp_setLatestConfiguration true r γ
    simp only [↓reduceIte] at hslc
    wp_apply hslc $$ [$Hcfgs $Hlatest $Hss1] as ⟨Hcfgs, Hss1, %pc, %cfg', Hlp, #Hpc, Hss2⟩
    ihave Hlatest : (∃ p : Loc, sync.atomic.ownPointer (T' := Configuration)
        (r.[Raft, go!"latestConfiguration"]) (DFrac.own 1) p ∗ p ↦□ cfg' : IProp GF) $$ [Hlp]
    · iexists pc; iframe; iframe #
    have hidx1 : lv1.Index' = W64 1 := by
      apply BitVec.eq_of_toNat_eq; simpa using Hlv1i
    rw [hidx1]
    wp_for_post
    iframe
    iexists _
    iframe
    iright
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists cfg, cfg'
    iframe
  -- after the scan
  -- the configurations after the scan: the genesis's (a bootstrap voter) or none (a non-member)
  have hent1 : ent [γ.g] 1 = some γ.g := by simp [ent]
  have hlc1 : lastCfgIdx [γ.g] = 1 := by
    have := lastCfgIdx_append_cfg [] γ.g hgk; simpa using this
  have hlc0 : lastCfgIdx ([] : RLog) = 0 := by
    have := (lastCfgIdx_spec ([] : RLog)).1; simpa using this
  ihave Hcf : (|==> ∃ (ccfg cfg : Configuration) (cidx li : w64) (pc : Loc),
      r.[Raft, go!"configurations"] ↦ configurations.mk ccfg cidx cfg li ∗
      cfgAtIs γ L0 (uint.nat li) cfg ∗ cfgAtIs γ L0 (uint.nat cidx) ccfg ∗
      ⌜uint.nat li = lastCfgIdx L0 ∧
        (cidx = li ∨ (uint.nat cidx = lastCfgIdx (L0.take (uint.nat li - 1)) ∧ 0 < uint.nat li)) ∧
        cidx = W64 0⌝ ∗
      sync.atomic.ownPointer (T' := Configuration) (r.[Raft, go!"latestConfiguration"])
        (DFrac.own 1) pc ∗
      (⌜pc = null⌝ ∨ ∃ c' : Configuration, pc ↦□ c' ∗ cfgOpt γ c') : IProp GF) $$ [Hst]
  · icases Hst with (⟨%Hidx, Hcfgs, Hlatest⟩ | ⟨⟨%Hidx, %hL⟩, %cfg, %cfg', Hcfgs, Hss1, Hlatest, Hss2⟩)
    · -- no iteration: a non-member, with an empty log
      subst Hidx
      have hL : L0 = [] := by
        rcases hshape with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · subst h; exfalso; apply Hif; simp only [List.length_cons, List.length_nil] at HlvIdx; word
      subst hL
      imodintro
      iexists zero_val Configuration, zero_val Configuration, W64 0, W64 0, null
      iframe
      isplitr
      · unfold cfgAtIs; ileft; isplitr; · ipureintro; rfl
        iapply ownSlice_nil
      isplitr
      · unfold cfgAtIs; ileft; isplitr; · ipureintro; rfl
        iapply ownSlice_nil
      isplitr
      · ipureintro; exact ⟨by rw [hlc0]; rfl, Or.inl rfl, rfl⟩
      ileft; ipureintro; rfl
    · -- the genesis processed: a bootstrap voter
      subst Hidx hL
      imod ownSlice_persist $$ Hss1 with #Hss1
      imod ownSlice_persist $$ Hss2 with #Hss2
      icases Hlatest with ⟨%pc, Hlp, #Hpc⟩
      imodintro
      iexists zero_val Configuration, cfg, W64 0, W64 1, pc
      iframe
      have hgd : γ.g.data = encodeServers ss := by rw [Hgss]; rfl
      isplitr
      · unfold cfgAtIs; iright; iexists ss, γ.g
        unfold cfgVal; iframe #
        ipureintro; exact ⟨Hss, by decide, hent1, hgk, hgd⟩
      isplitr
      · unfold cfgAtIs; ileft; isplitr; · ipureintro; rfl
        iapply ownSlice_nil
      isplitr
      · ipureintro
        refine ⟨by rw [hlc1]; rfl, Or.inr ⟨?_, by decide⟩, rfl⟩
        show 0 = lastCfgIdx (List.take (uint.nat (W64 1) - 1) [γ.g])
        rw [show uint.nat (W64 1) - 1 = 0 from rfl, List.take_zero, hlc0]
      iright; iexists cfg'; iframe #
      unfold cfgOpt; iexists ss; iframe #; ipureintro; right; exact Hss
  imod Hcf with ⟨%ccfg, %cfg, %cidx, %li, %pc, Hcfgs, #Hli, #Hcidx0, %Hcfgf, Hlp, Hpc⟩
  ------------------------------------------------------------------
  -- building `isRaft`: the locks
  imod sync.init_RWMutex_threadPool_low (leaderLockP r) leaderLockN (r.[Raft, go!"leaderLock"]) γLL
    hb $$ [leaderAddr leaderID] HllIs HllSt HllToks with ⟨%γpLL, #HllGuard, #HllPool⟩
  · inext; unfold leaderLockP; iexists _, _; iframe
  imod sync.init_RWMutex_qpool (lastContactP r) (E := ⊤) lastContactLockN
    (r.[Raft, go!"lastContactLock"]) hb $$ [lastContact] lastContactLock
    with ⟨%γpLC, #HlcGuard, #HlcPool⟩
  · inext; unfold lastContactP; iexists _; iframe
  imod sync.init_RWMutex_qpool (observersP γ i r) (E := ⊤) observersLockN
    (r.[Raft, go!"observersLock"]) hb $$ [observers HobsM] observersLock
    with ⟨%γpOL, #HolGuard, #HolPool⟩
  · inext; unfold observersP; iexists _, _; iframe
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- the routines group
  imod sync.init_WaitGroup (rgN.@"wg") _ $$ routinesGroup with ⟨%γwg, #HwgIs, Hwg, HwgW⟩
  imod qbank_alloc (GF := GF) with ⟨%γqb, Hqb⟩
  imod inv_alloc (rgN.@"inv") ⊤ (rgInv γwg γqb) $$ [Hwg HwgW Hqb] with #HrgInv
  · inext; unfold rgInv; iexists 0; iframe
  -- the cells
  iStructNamed leaderState
  imod inv_alloc termN ⊤ iprop(∃ t : w64,
      r.[Raft, go!"raftState"].[raftState, go!"currentTerm"] ↦ t ∗ termCouple γ i (uint.nat t))
    $$ [FcurrentTerm Hterm] with #HtermCell
  · inext; iexists _; iframe FcurrentTerm
    rw [show uint.nat (W64 (t0 : Int)) = t0 by
      rcases hshape with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> subst h <;> rfl]; iexact Hterm
  imod inv_alloc cidxN ⊤ iprop(∃ c : w64,
      r.[Raft, go!"raftState"].[raftState, go!"commitIndex"] ↦ c ∗ cidxCouple γ i (uint.nat c))
    $$ [FcommitIndex Hcidx] with #HcidxCell
  · inext; iexists _; iframe FcommitIndex
    rw [show uint.nat (zeroValDef : raftState).commitIndex' = 0 from rfl]; iexact Hcidx
  imod inv_alloc logN ⊤ iprop(∃ (A : LogAbs) (L ps : RLog) (lo c : Nat), rc.ownL A ∗
      logCouple γ i (L ++ ps) ∗ ghostVar rc.names.logPend (1 : Qp).half ps ∗
      ⌜(∀ k e, A.m.lookup k = some e → ent L k = some e) ∧
        (∀ k, lo ≤ k → k ≤ L.length → A.m.lookup k = ent L k)⌝ ∗
      compLb rc c ∗ ⌜lo ≤ c + 1⌝)
    $$ [HownL Hlogc Hglp'] with #HlogCell
  · inext; iexists _, L0, [], 1, 0; simp only [List.append_nil]; iframe
    unfold compLb; iframe #
    ipureintro
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · intro k e hk; rw [hstore] at hk; exact hk
    · intro k _ _; exact hstore k
  imod inv_alloc stateN ⊤ iprop(∃ st : w32,
      r.[Raft, go!"raftState"].[raftState, go!"state"] ↦ st ∗
      ghostVar rc.names.state (1 : Qp).half st ∗
      ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝)
    $$ [Fstate Hgst'] with #HstateCell
  · inext; iexists _; iframe; ipureintro; left; rfl
  imod inv_alloc appliedN ⊤ iprop(∃ a : w64,
      r.[Raft, go!"raftState"].[raftState, go!"lastApplied"] ↦ a ∗
      monoNatAuthOwn rc.names.applied (1 : Qp).half (uint.nat a))
    $$ [FlastApplied Hgap'] with #HappliedCell
  · inext; iexists _; iframe FlastApplied
    rw [show uint.nat (zeroValDef : raftState).lastApplied' = 0 from rfl]; iexact Hgap'
  imod inv_alloc cftN ⊤ iprop(∃ b : Bool, sync.atomic.ownBool
      (r.[Raft, go!"candidateFromLeadershipTransfer"]) (DFrac.own 1) b)
    $$ [candidateFromLeadershipTransfer] with #HcftCell
  · inext; iexists false; rw [sync.atomic.ownBool_unseal]; unfold sync.atomic.ownBoolDef
    rw [show (zeroValDef : sync.atomic.Bool') =
      ({ «_#0'» := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') from rfl]
    iexact candidateFromLeadershipTransfer
  imod inv_alloc ltipN ⊤ iprop(∃ v : w32, r.[Raft, go!"leaderState"].[leaderState,
      go!"leadershipTransferInProgress"] ↦ v)
    $$ [leadershipTransferInProgress] with #HltipCell
  · inext
    iexists (W32 0)
    rw [show (zeroValDef : leaderState).leadershipTransferInProgress' = W32 0 from rfl]
    iexact leadershipTransferInProgress
  -- the channels
  imod start_bag (V := Loc) (applyP γ rc i) ChanState.Idle applyCh γapply trivial $$ HapplyCh HapplyOwn
    with #HapplyBag
  imod start_bag (V := Unit) (fun _ => iprop(False)) ChanState.Idle sdCh γsd trivial $$ HsdCh HsdOwn
    with #HsdBag
  imod start_bag (V := Loc) (snapReqP γ rc) ChanState.Idle snapCh γsnap trivial
    $$ HsnapCh HsnapOwn with #HsnapBag
  imod start_bag (V := Loc) (ccfP γ) ChanState.Idle ccCh γcc trivial
    $$ HccCh HccOwn with #HccBag
  imod start_bag (V := Loc) userSnapP ChanState.Idle usCh γus trivial
    $$ HusCh HusOwn with #HusBag
  imod start_bag (V := Loc) (fun _ => iprop(False)) ChanState.Idle urCh γur trivial
    $$ HurCh HurOwn with #HurBag
  imod start_bag (V := Loc) (verifyP γ rc i vCh) (ChanState.Buffered []) vCh γv trivial
    $$ HvCh HvOwn with #HvBag
  imod start_bag (V := Loc) (cfgReqP γ rc i) (ChanState.Buffered []) cfgsCh γcfgs trivial
    $$ HcfgsCh HcfgsOwn with #HcfgsBag
  imod start_bag (V := Loc) (fun _ => iprop(False)) ChanState.Idle bsCh γbs trivial
    $$ HbsCh HbsOwn with #HbsBag
  imod start_bag (V := Loc) (ltfP γ i) (ChanState.Buffered []) ltCh γlt trivial
    $$ HltCh HltOwn with #HltBag
  imod start_bag (V := Unit) (fun _ => iprop(False)) (ChanState.Buffered []) lnCh γln trivial
    $$ HlnCh HlnOwn with #HlnBag
  imod start_bag (V := Unit) (fun _ => iprop(False)) (ChanState.Buffered []) fnCh γfn trivial
    $$ HfnCh HfnOwn with #HfnBag
  -- the immutable fields
  ipersist protocolVersion
  ipersist localID
  ipersist localAddr
  ipersist preVoteDisabled
  ipersist noLegacyTelemetry
  ipersist stable
  ipersist trans
  ipersist rpcCh
  ipersist fsm
  ipersist applyCh
  ipersist fsmMutateCh
  ipersist leaderCh
  ipersist shutdownCh
  ipersist fsmSnapshotCh
  ipersist configurationChangeCh
  ipersist userSnapshotCh
  ipersist userRestoreCh
  ipersist verifyCh
  ipersist configurationsCh
  ipersist bootstrapCh
  ipersist leadershipTransferCh
  ipersist leaderNotifyCh
  ipersist followerNotifyCh
  imod (sync.atomic.ownValue_dfractional (GF := GF) _ _).dfractional_persist (DFrac.own 1) $$ Hconfv
    with #Hconfv
  imod inv_alloc latestCfgN ⊤ (latestCfgCell r γ) $$ [Hlp Hpc] with #HlatInv
  · inext; unfold latestCfgCell
    iexists pc; iframe
  -- (stage 3) the snapshot store's invariant: nothing stored, no install pending
  imod snapCell_alloc rc γ i $$ [$HownSS $Hpend'] with #HsnapCell
  ihave #Hraft : (isRaft r γ rc i : IProp GF) $$ []
  · rw [isRaft_unseal]; unfold isRaftDef
    isplitr; · iexact Hinv
    isplitr; · iexact Hvoter
    isplitr
    · unfold raftImm; rw [hLID] at *; iframe #
    isplitr
    · unfold raftIfaces
      iexists logsI, stableI, snapsI, transI, fsmI, rpcCh, eof
      iframe #
      repeat' (first
        | iexact Hfsm
        | iexact Hsnaps
        | iexact Heof
        | iexact HlogsC
        | (unfold isLogStore getLogPost; iexact HlogsC)
        | iexact HstableC
        | (unfold isStableStore; iexact HstableC)
        | iexact HtransC
        | (unfold isTransport; iexact HtransC)
        | (ipureintro; first | exact Hnmono | exact Hpv | exact Hnb | exact ⟨Hpv, Hnb⟩)
        | isplitr)
    isplitr
    · unfold raftConf
      iexists c
      iframe #
      ipureintro; exact ⟨hPV, hLID, hi, hNC, hBA, hPVD, hSkip, hRCL, hNSR, hMA1, hMA2,
        hHB1, hHB2, hCT, hSI, hLL1, hLL2, hET, hHT, hCT2, hSI2⟩
    isplitr
    · unfold raftCells termCell cidxCell logCell stateCell appliedCell cftCell ltipCell
      iframe #
    isplitr
    · unfold raftLocks rwLock lastLockInv
      iframe #
      unfold rgOk; iexists γwg, γqb; iframe #; ipureintro; exact hb
    isplitr
    · unfold raftChans deadField deadChan
      iframe #
    · ipureintro; exact Hcv
  -- the heartbeat fast path: the transport may call `r.processHeartbeat` from now on
  wp_bind (App (Val #(methods _ _ _)) _)
  iapply HSetHB
  · iapply hbHandler_intro
    iintro !> %v %tid' %Φ' Hv Htok' HΦ'
    iapply wp_processHeartbeat r γ rc i v tid' $$ %Φ' [$Hpkg $Hraft $Hv $Htok'] HΦ'
  wp_auto
  rw [hSkip]
  wp_auto
  -- the main goroutine's resources
  have hlast : (uint.nat lv.Index', uint.nat lv.Term') = (L0.length, lastTerm L0) := by
    rw [HlvIdx.1, HlvIdx.2]
  obtain ⟨Hli0, Hcfgf1, Hcidx0⟩ := Hcfgf
  subst Hcidx0
  ihave #HcmtIdx := cmtIdx_zero (γ := γ) t0 L0
  ihave Hmain : (mainOwn r γ rc i : IProp GF) $$ [Hsrv Hdur HownS Hgll Hgst Hgap HfsmProd Hgb Hcfgs
      HlchOwn Hglp Hvtok Hvreg Hvlive Hvnm Hpend Hcomp]
  · unfold mainOwn
    iexists (SState.mk t0 L0 0 [] (0, 0) 0), (W32 0)
    isplitl [Hsrv Hdur HownS Hgll Hgst Hgap HfsmProd Hgb Hcfgs HlchOwn Hglp Hvtok Hvreg Hvlive Hvnm
      Hpend Hcomp]
    rotate_left
    · ileft; ipureintro; decide
    unfold mainOwnAt
    iexists 0, _, cfg, ccfg, W64 0, li, leaderCh, γlch, [], 0
    simp only
    rw [← hlast]
    iframe
    iframe #
    isplitr
    · ipureintro; unfold voteMatches
      refine ⟨?_, Or.inl rfl⟩
      show uint.nat ((<[_ := W64 (t0 : Int)]> sst.ints !! _).getD (W64 0)) = 0
      rw [GMap.lookup_insert_ne _ _ (by decide)]
      have h2 := Hsst.2
      rw [show sst.ints !! (go!"LastVoteTerm" : List w8) = none from h2]; rfl
    isplitr
    · ileft; ipureintro; decide
    isplitl [Hvtok Hvreg Hvlive Hvnm]
    · unfold verifyRegistry
      iexists ∅, ∅, ∅, ∅
      iframe
      isplitr
      · ipureintro; simp
      isplitr
      · iapply BigSepM.bigSepM_empty.2; iempintro
      · iapply BigSepM.bigSepM_empty.2; iempintro
    isplitr
    · ipureintro; simp
    isplitl [HfsmProd Hgb]
    · unfold fsmProd; iexists [], ∅, 0; iframe
      isplitr
      · ipureintro; simp
      isplitr
      · ileft; ipureintro; simp
      unfold noCmdBetween; simp; iempintro
    repeat' (first
      | iexact HcmtIdx
      | (rw [show uint.nat (W64 0) = 0 from rfl]; iexact HcmtIdx)
      | (ipureintro; first | exact Nat.le_refl 0 | exact ⟨Hli0, Hcfgf1⟩ | (rw [HlchCap]; simp))
      | isplitr)
  ihave HlsAny : (leaderStateAny r rc : IProp GF) $$ [commitCh commitment inflight replState notify
      stepDown Hvnm']
  · unfold leaderStateAny; iexists _, _, _, _, _, _; iframe
  -- r.goFunc(r.run)
  wp_apply (wp_goFunc r γ rc i _ tid) $$ [$Hraft $Htok Hmain HlsAny] as Htok
  · iintro %tid' Htok'
    wp_apply (wp_run r γ rc i tid') $$ [$Hraft $Hmain $HlsAny $Htok'] as Hf
    iexfalso; iexact Hf
  -- r.goFunc(r.runFSM)
  wp_apply (wp_goFunc r γ rc i _ tid) $$ [$Hraft $Htok HfsmCons HfsmOwn] as Htok
  · iintro %tid' Htok'
    wp_apply (wp_runFSM r γ rc i tid') $$ [$Hraft $Htok' HfsmCons HfsmOwn] as Hf
    · unfold fsmCons; iframe
    iexfalso; iexact Hf
  -- r.goFunc(r.runSnapshots)
  wp_apply (wp_goFunc r γ rc i _ tid) $$ [$Hraft $Htok] as Htok
  · iintro %tid' Htok'
    wp_apply (wp_runSnapshots r γ rc i tid') $$ [$Hraft $Htok'] as Hf
    iexfalso; iexact Hf
  wp_end
  iframe
  iexists rc.names
  iexact Hraft
  done

end proof

end Perennial
