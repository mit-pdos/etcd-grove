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

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
/-- (stage 3) A fresh snapshot store's invariant: nothing stored, no install pending. -/
theorem snapCell_alloc (rc : github_com.hashicorp.raft.RCtx GF) (γ : github_com.hashicorp.raft.gprot.GNames)
    (i : github_com.hashicorp.raft.proto.SID) :
    rc.ownSS none ∗ ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ⊢
      |={⊤}=> github_com.hashicorp.raft.snapCell rc γ i := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
-/

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
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

end proof

end Perennial
