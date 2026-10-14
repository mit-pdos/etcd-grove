/-
The refinement of the dynamic model (2026-10-14, reconfiguration stage B5): the ghost state, in
its dynamic mode (`RaftNames.reDyn = some (DynCfg.ofFold dec c0 h0)`: the configuration of a
committed prefix is its fold from `c0`), follows `StepR` steps with configurations changing by
applied conf entries (`Adm := AdmFold dec c0`, with the snapshot prefixes' records, below).

* `DynCfg.ofFold dec c0 h0`: the mode's configurations, `cfgFold dec c0`, with `fold_adjacent`
  for the one fact the ghost state uses (`DynCfg.adj`).
* `ownRaftGhostR γ dec c0 id r`: the node's ghost state in the dynamic mode (`ownRaftGhost ... true`)
  over `r.p`, with `RInv dec c0 r` (stage B3's invariant: the configuration is the fold of the
  full log's first `cidx` entries, I1, I3, the campaign guard), the records of `r.fp` (so it is
  the ghost state's full prefix, `FullOk_unique`), and a candidate's campaign record of its full
  log at its commit index.
* `ownRaftGhostR_env`: the step environment (`dynEnv`) the configuration-reading rules take,
  from `RInv`.
* `ownRaftGhostR_stepR`: every `StepR` derivation updates it, given the messages it consumed,
  their read credits, and the records of every snapshot prefix the derivation may restore
  (`S`, see below).

**The snapshot prefixes.** `StepR.snapRestore` takes the restored node's new full prefix `fp'`
from the rule, constrained only by `FullOk` and `Adm fp' cs'` (B3). A run whose `fp'` is not the
committed prefix the snapshot covers is not one of a real system (A3: the snapshot's
`ConfState` is its prefix's configuration, and later decoded conf entries depend on the prefix),
and the ghost state cannot follow it. The refinement therefore takes, for the derivation's
admissible prefixes `S`, their records (`□ ∀ fp, ⌜S fp⌝ -∗ logRecs γ base0 fp`): with records and
`FullOk`, `fp'` is the sender's committed prefix. The code (stage B7) chooses `fp'` from the
message's knowledge and supplies them.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.Refinement
public import Proof.go_etcd_io.raft.v3.Protocol.StepRInv

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section dyn
variable [FfiSyntax]

/-- The dynamic configurations of a decoder and an initial configuration with `CfgOk`. -/
def DynCfg.ofFold (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0) : DynCfg where
  fold P := (cfgFold dec c0 P).map (fun s => s.cfg)
  adj := by
    intro P1 P2 c1 c2 hp hc h1 h2
    obtain ⟨M, rfl⟩ := hp
    cases e1 : cfgFold dec c0 P1 with
    | none => rw [e1] at h1; cases h1
    | some s1 =>
      cases e2 : cfgFold dec c0 (P1 ++ M) with
      | none => rw [e2] at h2; cases h2
      | some s2 =>
        rw [e1] at h1; rw [e2] at h2
        simp only [Option.map_some, Option.some.injEq] at h1 h2
        subst h1 h2
        refine fold_adjacent dec (P1 ++ M) P1.length (P1 ++ M).length c0 s1 s2
          (by simp) ?_ h0 ?_ ?_
        · rw [List.take_length, List.take_left']
          · exact hc
          · rfl
        · rw [List.take_left']; exact e1; rfl
        · rw [List.take_length]; exact e2

/-- The configurations the dynamic model admits after a prefix: its fold (A3), among the
prefixes `S` (whose records the refinement takes, see the file header). -/
def AdmS (dec : CCDec) (c0 : CCState) (S : List raftpb.Entry → Prop) (l : List raftpb.Entry)
    (cs : CCState) : Prop :=
  AdmFold dec c0 l cs ∧ S l

theorem toNat_uZ (w : w64) : (uint.Z w).toNat = uint.nat w := by
  have := rUnat_eq w; omega

theorem cfgAt_of_fold {γ : RaftNames} {dec : CCDec} {c0 : CCState} {h0 : CfgOk c0}
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) {P : List raftpb.Entry} {s : CCState}
    (h : cfgFold dec c0 P = some s) : CfgAt γ P s.cfg :=
  CfgAt.of_dyn HD (by simp [DynCfg.ofFold, h])

theorem reDyn_of {γ : RaftNames} {D : DynCfg} (HD : γ.dyn = some D) : γ.reDyn ≠ none := by
  intro h; rw [RaftNames.dyn_none h] at HD; cases HD

/-- No `MsgApp` received. -/
theorem noApp1 {dec : CCDec} {c0 : CCState} {m : Msg} (h : m.ty ≠ .app) :
    ∀ (r1 : RState) (m' : Msg), m' ∈ [m] → m'.ty = .app → RInv dec c0 r1 → AppKnow r1 m' := by
  intro r1 m' hm hty _
  rw [List.mem_singleton] at hm; subst hm; exact absurd hty h

theorem noApp0 {dec : CCDec} {c0 : CCState} :
    ∀ (r1 : RState) (m' : Msg), m' ∈ ([] : List Msg) → m'.ty = .app → RInv dec c0 r1 →
      AppKnow r1 m' := by
  intro r1 m' hm; cases hm

end dyn

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

/-- A node's ghost state in the dynamic mode, with its reconfiguration state (see the file
header). -/
def ownRaftGhostR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64) (r : RState) :
    IProp GF :=
  iprop(ownRaftGhost γ id r.p true ∗ ⌜RInv dec c0 r⌝ ∗ logRecs γ base0 r.fp ∗
    (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit))

/-- The step environment, from `RInv`: the full prefix, I1, the configuration index (the
commit index at a candidate, `RInv.cand_cfg`), I3 at a leader. -/
theorem ownRaftGhostR_env (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (id : w64) (r : RState)
    (HI : RInv dec c0 r) :
    ⊢ logRecs (GF := GF) γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      dynEnv γ id r.cfg.cfg r.p := by
  iintro #Hfr #Hc
  unfold dynEnv
  iright
  isplitr
  · ipureintro; exact reDyn_of HD
  have Hcl : r.cidx < 2 ^ 64 := by
    have := HI.cidx_commit; have := rUnat_eq r.p.commit; have := uint_Z_lt r.p.commit; omega
  by_cases hc : r.p.role = .candidate
  · iexists r.fp, r.p.commit
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, Int.le_refl _, ?_, ?_, fun _ => rfl⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [toNat_uZ]; exact cfgAt_of_fold HD (HI.cand_cfg hc).1
      · intro hl; rw [hc] at hl; cases hl
    · rw [show r.fp ++ r.p.log = r.full from rfl]; iexact Hc
  · iexists r.fp, (W64 (r.cidx : Int))
    have Hw : (uint.Z (W64 (r.cidx : Int))).toNat = r.cidx := by
      rw [uint_Z_W64 _ (by omega) (by omega)]; simp
    iframe Hfr
    isplitr
    · ipureintro
      refine ⟨HI.full, ?_, ?_, ?_, ?_, fun h => absurd h hc⟩
      · rw [toNat_uZ]; exact HI.i1
      · rw [uint_Z_W64 _ (by omega) (by omega)]
        have := HI.cidx_commit; have := rUnat_eq r.p.commit; omega
      · rw [Hw]; exact cfgAt_of_fold HD HI.cfg
      · intro hl; rw [Hw]; exact HI.leader_drop_cidx hl
    · iintro %h; exact absurd h hc

/-- Closing a step that keeps the full prefix, and a candidate's campaign record. -/
theorem ownRaftGhostR_close (γ : RaftNames) (dec : CCDec) (c0 : CCState) (id : w64)
    (r r' : RState) :
    ⊢ ⌜RInv dec c0 r'⌝ -∗ ⌜r'.fp = r.fp⌝ -∗
      ⌜r'.p.role = .candidate →
        r.p.role = .candidate ∧ r'.p.term = r.p.term ∧ r'.p.log = r.p.log ∧
          r'.p.commit = r.p.commit⌝ -∗
      ownRaftGhost (GF := GF) γ id r'.p true -∗ logRecs γ base0 r.fp -∗
      (∀ (_ : r.p.role = .candidate), isCampK γ id r.p.term r.full r.p.commit) -∗
      ownRaftGhostR γ dec c0 id r' := by
  iintro %HI' %Hfp %Hcand Hg #Hfr #Hc
  unfold ownRaftGhostR
  iframe Hg
  isplitr; · ipureintro; exact HI'
  isplitr; · rw [Hfp]; iexact Hfr
  iintro %hc
  obtain ⟨hc0, ht, hl, hcm⟩ := Hcand hc
  ihave #Hk := Hc $$ %hc0
  unfold RState.full
  rw [Hfp, ht, hl, hcm]
  iexact Hk


/-- The dynamic refinement (2026-10-14, stage B5): a `StepR` derivation at the dynamic
configurations (`AdmS dec c0 S`: the fold of the prefix, among `S`) updates the node's
dynamic ghost state, given the messages it consumed with their read credits and the records of
the prefixes `S` (see the file header). -/
theorem ownRaftGhostR_stepR (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (HD : γ.dyn = some (DynCfg.ofFold dec c0 h0)) (S : List raftpb.Entry → Prop)
    (id : w64) (r : RState) (recv : List Msg) (r' : RState) :
    StepR (AdmS dec c0 S) dec id r recv r' →
    ⊢ (□ ∀ (fp : List raftpb.Entry), ⌜S fp⌝ -∗ logRecs (GF := GF) γ base0 fp) -∗
      ([∗list] m ∈ recv, isMessage γ m) -∗ rdCred γ (rdCount recv) -∗
      ownRaftGhostR γ dec c0 id r ={⊤}=∗ ownRaftGhostR γ dec c0 id r' := by
  intro Hstep
  induction Hstep with
  | refl r =>
    iintro _ _ - Hown
    imodintro; iexact Hown
  | trans r0 m1 r1 m2 r2 _ _ IH1 IH2 =>
    iintro #HS Hrecv Hcr Hown
    icases (BigSepL.bigSepL_append (Φ := fun _ m => isMessage (GF := GF) γ m)).1 $$ Hrecv with
      ⟨Hr1, Hr2⟩
    rw [rdCount_append]
    icases (rdCred_split γ (rdCount m1) (rdCount m2)).1 $$ Hcr with ⟨Hc1, Hc2⟩
    imod IH1 $$ HS Hr1 Hc1 Hown with Hown
    iapply IH2 $$ HS Hr2 Hc2 Hown
  | higherTerm m r h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_higherTerm γ id m r.p h1 h2 h3 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | grantVote m r h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_grantVote γ id m r.p h1 h2 h3 h4 h5 h6 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.grantVote m r h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | rejectVote m r h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_rejectVote γ id m r.p h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.rejectVote m r h1 h2) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | recordVote m r h1 h2 h3 h4 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_recordVote γ id m r.p h1 h2 h3 h4 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.recordVote m r h1 h2 h3 h4) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | lose r h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_lose γ r.cfg.cfg id r.p h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.lose r h1 h2) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | drain r o' h1 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_drain γ id r.p o' h1 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.drain r o' h1) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | takeReads r =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_takeReads γ id r.p $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.takeReads r) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | sendFree r m h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_sendFree γ id r.p m h1 h2 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.sendFree r m h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | abandon r h1 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_abandon γ id r.p h1 $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.abandon r h1) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | zeroAck r dst =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_zeroAck γ id r.p dst $$ Hrecv Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.zeroAck r dst) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | appStale m r h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_stale γ id r.p m h1 h3 h4 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (by first | exact RInv_keep _ HI rfl rfl rfl (Or.inr rfl) | exact RInv_keep _ HI rfl rfl rfl (Or.inl rfl) | exact HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | appReject m r hint hintterm h1 h2 h3 h4 h5 h6 h7 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_reject γ id r.p m hint hintterm h1 h3 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (by first | exact RInv_keep _ HI rfl rfl rfl (Or.inr rfl) | exact RInv_keep _ HI rfl rfl rfl (Or.inl rfl) | exact HI.frame rfl rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl))
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | heartbeat m r h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_heartbeat γ id r.p m h1 h2 h4 h3 h5 h6 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.heartbeat m r h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | appResp m r x h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_resp γ id r.p m x h1 h3 h4 h5 h6 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.appResp m r x h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | propForward m r h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_prop_forward γ id r.p m h1 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propForward m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | snapFastfwd m r h1 h2 h3 h4 h5 h6 h7 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_snap_fastfwd γ id r.p m h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapFastfwd m r h1 h2 h3 h4 h5 h6 h7) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | snapStale m r h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_snap_stale γ id r.p m h1 h3 h4 h5 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapStale m r h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | readState m r e h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_read_state γ id r.p m e h1 h2 $$ Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readState m r e h1 h2) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | beat r ms h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_beat γ id r.p ms h1 h2 h3 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.beat r ms h1 h2 h3) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | reMatch r mt h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_rematch γ id r.p mt h1 h2 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.reMatch r mt h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readRelease r h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imod ownRaftGhost_step_read_release γ id r.p h1 h2 $$ Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readRelease r h1 h2) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readFwd m r h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_fwd γ id r.p m h1 h2 h3 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readFwd m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readPend m r pm h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_pend γ id r.p m pm h1 h2 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readPend m r pm h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readArrive m r h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    rw [show rdCount [m] = 1 by simp [rdCount_singleton, h1]]
    imod ownRaftGhost_step_read_arrive γ id r.p m h1 h2 h3 $$ Hm Hcr Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readArrive m r h1 h2 h3) (noApp1 (by rw [h1]; decide)) HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | win r mt ms h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_win γ r.cfg.cfg id r.p mt ms h1 h2 h3 h4 h5 (fun _ => h6) $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.win r mt ms h1 h2 h3 h4 h5 h6) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | commit r n h1 h2 h3 h4 h5 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_commit γ r.cfg.cfg id r.p n h1 h2 h3 h4 h5 $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.commit r n h1 h2 h3 h4 h5) noApp0 HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | sendApps r ms h1 h2 h3 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_send_apps γ r.cfg.cfg id r.p ms h1 h2 (fun _ => h3) $$ Henv Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.sendApps r ms h1 h2 h3) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | readAck m r N h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_read_ack γ r.cfg.cfg id r.p m N h1 h2 h3 h4 h5 h6 $$ Henv Hm Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.readAck m r N h1 h2 h3 h4 h5 h6) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | campaign r peers cl h1 h2 h3 h4 h5 h6 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Henv := ownRaftGhostR_env γ dec c0 h0 HD id r HI $$ Hfr Hc
    imod ownRaftGhost_step_campaign γ r.cfg.cfg id r.p peers cl h1 h2 h5 h6 $$ Henv Hrecv Hcr Hg
      with ⟨Hg, %fpc, %Hfpc, #Hfrc, #HcK⟩
    icases FullOk_unique γ r.p.base fpc r.fp Hfpc HI.full $$ Hfrc Hfr with %Heq
    subst Heq
    imodintro
    unfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro
      exact RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.campaign r peers cl h1 h2 h3 h4 h5 h6) noApp0 HI
    iintro %_
    dsimp only [psendMsgs, pbecomeCandidate, RState.full]
    iexact HcK
  | propose m r cs h1 h2 h3 h4 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    iunfold isMessage at Hm
    rw [h1]
    icases Hm with ⟨-, #Hed⟩
    have hrep : PropRepl m.entries (propBatch r m.entries cs).1 :=
      propConf_repl (joint := CfgM.joint r.cfg.cfg) r.applied (plastIndex r.p) r.pci m.entries cs h3
    ihave #Hed' := entData_propRepl γ _ _ hrep $$ Hed
    imod ownRaftGhost_step_propose γ id r.p (propBatch r m.entries cs).1 h2
      (by rw [hrep.length]; exact h4) $$ Hed' Hg with Hg
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propose m r cs h1 h2 h3 h4) (noApp1 (by rw [h1]; decide)) HI)
    iintro %h
    exfalso
    revert h
    first
      | (simp [psendMsgs, pbecomeFollower, padoptLeader, pwinState, pappend, pbecomeLeader]; done)
      | (intro h; rw [preadRespondAll_role] at h; simp at h; simp_all)
      | (intro h; simp_all)
  | propDrop m r cs h1 h2 h3 h4 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.propDrop m r cs h1 h2 h3 h4) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | advance r a h1 h2 h3 h4 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.advance r a h1 h2 h3 h4) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | applySnap r h1 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.applySnap r h1) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    imodintro
    iunfold ownRaftGhostR
    iframe Hg Hfr
    isplitr
    · ipureintro; exact (RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.applyConf r k e op cs' h1 h2 h3 h4 h5 h6 h7 h8 h9) noApp0 HI)
    dsimp only [psendMsgs, RState.full, pappend]
    iexact Hc
  | snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_snap_restore γ id r.p m h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    ihave #Hfr' := HS $$ %fp' %h10.2
    imodintro
    unfold ownRaftGhostR
    iframe Hg Hfr'
    isplitr
    · ipureintro
      exact RInv_stepR (Adm := AdmS dec c0 S) (id := id) (fun _ _ h => h.1) (StepR.snapRestore m r fp' cs' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
        (noApp1 (by rw [h1]; decide)) HI
    iintro %h
    simp [psendMsgs, padoptLeader] at h
  | appAccept m r lastnewi es' h1 h2 h3 h4 h5 h6 h7 h8 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    ihave #Hm := recv_one γ _ $$ Hrecv
    imod ownRaftGhost_step_app_accept γ id r.p m lastnewi es' h1 h3 h4 h5 h6 h7 $$ Hm Hg with Hg
    imodintro
    sorry
  | stepDown r h1 h2 =>
    iintro #HS Hrecv Hcr Hown
    iunfold ownRaftGhostR at Hown
    icases Hown with ⟨Hg, %HI, #Hfr, #Hc⟩
    sorry

end ghost

end EtcdGrove
end Perennial
