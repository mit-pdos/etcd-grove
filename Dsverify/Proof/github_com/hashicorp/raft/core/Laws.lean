/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/core/Laws.lean (241f27e).
-/
/-
Raft-internal interface: the laws of the shared predicates of `core/Defs.lean` (statements; the
proofs are CORE's, except the client-side future triples, API's).

* eliminations of the sealed `isRaft` (each component);
* the error values (`isRaftErr`) from `isPkgInit`;
* observers (`obsArg`);
* the FSM batch ghost map (`batchEnd_agree`);
* the client's side of a future returned by `Apply` (`wp_future_Error`): what hr3 calls through
  the `ApplyFuture` interface value.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Defs

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-! ## `isRaft` eliminations -/

section isRaft
variable (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID)

theorem isRaft_proto : isRaft r γ rc i ⊢ Inv γ ∗ isSrv γ i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨#H1, #H2, -⟩; iframe #

theorem isRaft_imm : isRaft r γ rc i ⊢ raftImm r i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, #H, -⟩; iexact H

theorem isRaft_ifaces : isRaft r γ rc i ⊢ raftIfaces r γ rc i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, #H, -⟩; iexact H

theorem isRaft_conf : isRaft r γ rc i ⊢ raftConf r γ i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, -, #H, -⟩; iexact H

theorem isRaft_cells : isRaft r γ rc i ⊢ raftCells r γ rc i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, -, -, #H, -⟩; iexact H

theorem isRaft_locks : isRaft r γ rc i ⊢ raftLocks r γ rc i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, -, -, -, #H, -⟩; iexact H

theorem isRaft_chans : isRaft r γ rc i ⊢ raftChans r γ rc i := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, -, -, -, -, #H, -⟩; iexact H

/-! ### `isRaftCore` (hraft_robust rcl) -/

/-- **`isRaft` is `isRaftCore` and the end of `NewRaft`'s `lastLock` pin.** -/
theorem isRaft_iff_core : isRaft r γ rc i ⊣⊢
    isRaftCore r γ rc i ∗ dghostVar rc.names.llb DFrac.discard (none : Option (w64 × w64 × w64 × w64)) := by
  rw [isRaft_unseal, isRaftCore_unseal]; unfold isRaftDef isRaftCoreDef raftCells raftCellsCore
  constructor
  · iintro ⟨#H1, #H2, #H3, #H4, #H5, ⟨#C1, #C2, #C3, #C4, #C5, #C6, #C7, #C8⟩, #H7, #H8, %H9⟩
    iframe #; ipureintro; exact H9
  · iintro ⟨⟨#H1, #H2, #H3, #H4, #H5, ⟨#C1, #C2, #C3, #C4, #C5, #C6, #C7⟩, #H7, #H8, %H9⟩, #C8⟩
    iframe #; ipureintro; exact H9

theorem isRaft_core : isRaft r γ rc i ⊢ isRaftCore r γ rc i :=
  (isRaft_iff_core r γ rc i).1.trans sep_elim_left

theorem isRaft_of_core :
    isRaftCore r γ rc i ∗ dghostVar rc.names.llb DFrac.discard (none : Option (w64 × w64 × w64 × w64)) ⊢
      isRaft r γ rc i :=
  (isRaft_iff_core r γ rc i).2

/-- `iframe`/`$H` prove `isRaftCore` from `isRaft`. -/
instance isRaft_frame_core (p : Bool) :
    Iris.ProofMode.Frame p (isRaft r γ rc i) (isRaftCore r γ rc i) iprop(emp) where
  frame := sep_emp.1.trans (intuitionisticallyIf_elim.trans (isRaft_core r γ rc i))

theorem isRaftCore_proto : isRaftCore r γ rc i ⊢ Inv γ ∗ isSrv γ i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨#H1, #H2, -⟩; iframe #

theorem isRaftCore_imm : isRaftCore r γ rc i ⊢ raftImm r i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨-, -, #H, -⟩; iexact H

theorem isRaftCore_ifaces : isRaftCore r γ rc i ⊢ raftIfaces r γ rc i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨-, -, -, #H, -⟩; iexact H

theorem isRaftCore_conf : isRaftCore r γ rc i ⊢ raftConf r γ i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨-, -, -, -, #H, -⟩; iexact H

theorem isRaftCore_cells : isRaftCore r γ rc i ⊢ raftCellsCore r γ rc i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨-, -, -, -, -, #H, -⟩; iexact H

theorem isRaftCore_chans : isRaftCore r γ rc i ⊢ raftChans r γ rc i := by
  rw [isRaftCore_unseal]; unfold isRaftCoreDef
  iintro ⟨-, -, -, -, -, -, -, #H, -⟩; iexact H

theorem isRaftCore_logStore : isRaftCore r γ rc i ⊢
    ∃ x : GoInterfaceOk, r.[Raft, go!"logs"] ↦□ (GoInterface.ok x) ∗ isLogStore x rc.ownL (logWin γ rc i) ∗
      ⌜go.typeSetContains x.ty MonotonicLogStore.ty = false⌝ := by
  iintro #H
  ihave #H2 := isRaftCore_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, #Hl, #Hli, %Hm, -⟩
  iexists l; iframe #; ipureintro; exact Hm

theorem isRaftCore_config : isRaftCore r γ rc i ⊢
    ∃ c : Config, sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard
      (interface.mkOk Config.ty #c) ∗ ⌜cfgOk c i⌝ := by
  iintro #H
  ihave #H2 := isRaftCore_conf r γ rc i $$ H
  unfold raftConf
  icases H2 with ⟨%c, #Hc, %Hok, -⟩
  iexists c; iframe #; ipureintro; exact Hok

theorem isRaftCore_fsmCh : isRaftCore r γ rc i ⊢
    ∃ ch : Loc, r.[Raft, go!"fsmMutateCh"] ↦□ ch ∗
      isSpsc (V := GoInterface) rc.names.fsmCh ch (fsmP γ rc i) (fun _ => iprop(False)) := by
  iintro #H
  ihave #H2 := isRaftCore_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, ⟨%ch, #Hch, #Hb⟩, -⟩
  iexists ch; iframe #

theorem isRaftCore_shutdownCh : isRaftCore r γ rc i ⊢ deadField Unit r go!"shutdownCh" := by
  iintro #H
  ihave #H2 := isRaftCore_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, -, -, -, -, #H3, -⟩; iexact H3

/-- (stage 4) The protocol's decoding of a configuration's voters is `DecodeConfiguration`'s. -/
theorem isRaft_cv : isRaft r γ rc i ⊢ ⌜γ.cv = cfgDec γ.srvs⌝ := by
  rw [isRaft_unseal]; unfold isRaftDef
  iintro ⟨-, -, -, -, -, -, -, -, %H⟩; ipureintro; exact H

theorem isRaft_logStore : isRaft r γ rc i ⊢
    ∃ x : GoInterfaceOk, r.[Raft, go!"logs"] ↦□ (GoInterface.ok x) ∗ isLogStore x rc.ownL (logWin γ rc i) ∗
      ⌜go.typeSetContains x.ty MonotonicLogStore.ty = false⌝ := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, #Hl, #Hli, %Hm, -⟩
  iexists l; iframe #; ipureintro; exact Hm

theorem isRaft_stableStore : isRaft r γ rc i ⊢
    ∃ x : GoInterfaceOk, r.[Raft, go!"stable"] ↦□ (GoInterface.ok x) ∗ isStableStore x rc.ownS (stWin γ rc i) := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, -, -, -, #Hs, #Hsi, -⟩
  iexists s; iframe #

theorem isRaft_snapshotStore : isRaft r γ rc i ⊢
    ∃ (x : GoInterfaceOk) (eof : GoInterface), r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok x) ∗
      isSnapStore x rc.ownSS eof (snapWin γ rc i) ∗ globalAddr io.EOF ↦□ eof := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, -, -, -, -, -, #Hs, #Hsi, #He, -⟩
  iexists sn, eof; iframe #

theorem isRaft_transport : isRaft r γ rc i ⊢
    ∃ (x : GoInterfaceOk) (rpcCh : Loc), r.[Raft, go!"trans"] ↦□ (GoInterface.ok x) ∗
      r.[Raft, go!"rpcCh"] ↦□ rpcCh ∗ isTransport x γ rc.snapP i rpcCh := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, -, -, -, -, -, -, -, -, #Ht, #Hti, %Hpv, #Hch, -⟩
  iexists t, ch; iframe #

/-- The transport implements `WithPreVote` (review R1). -/
theorem isRaft_transport_withPreVote : isRaft r γ rc i ⊢
    ∃ (x : GoInterfaceOk) (rpcCh : Loc), r.[Raft, go!"trans"] ↦□ (GoInterface.ok x) ∗
      r.[Raft, go!"rpcCh"] ↦□ rpcCh ∗ isTransport x γ rc.snapP i rpcCh ∗
      ⌜go.typeSetContains x.ty WithPreVote.ty = true⌝ := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, -, -, -, -, -, -, -, -, #Ht, #Hti, %Hpv, #Hch, -⟩
  iexists t, ch; iframe #; ipureintro; exact Hpv

theorem isRaft_fsm : isRaft r γ rc i ⊢
    ∃ x : GoInterfaceOk, r.[Raft, go!"fsm"] ↦□ (GoInterface.ok x) ∗
      isFSM x γ i rc.fsmOwn rc.respP rc.snapP ∗ ⌜fsmNotBatching x⌝ := by
  iintro #H
  ihave #H2 := isRaft_ifaces r γ rc i $$ H
  unfold raftIfaces
  icases H2 with ⟨%l, %s, %sn, %t, %f, %ch, %eof, -, -, -, -, -, -, -, -, -, -, -, -, #Hf, #Hfi, %Hnb⟩
  iexists f; iframe #; ipureintro; exact Hnb

theorem isRaft_config : isRaft r γ rc i ⊢
    ∃ c : Config, sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard
      (interface.mkOk Config.ty #c) ∗ ⌜cfgOk c i⌝ := by
  iintro #H
  ihave #H2 := isRaft_conf r γ rc i $$ H
  unfold raftConf
  icases H2 with ⟨%c, #Hc, %Hok, -⟩
  iexists c; iframe #; ipureintro; exact Hok

theorem isRaft_termCell : isRaft r γ rc i ⊢ termCell r γ rc i := by
  iintro #H
  ihave #H2 := isRaft_cells r γ rc i $$ H
  unfold raftCells
  icases H2 with ⟨#H3, -⟩; iexact H3

theorem isRaft_cidxCell : isRaft r γ rc i ⊢ cidxCell r γ rc i := by
  iintro #H
  ihave #H2 := isRaft_cells r γ rc i $$ H
  unfold raftCells
  icases H2 with ⟨-, #H3, -⟩; iexact H3

/-- (hraft_robust L0) The crash invariant (was `isRaft_durInv`/`isRaft_snapCell`). -/
theorem isRaft_durInv : isRaft r γ rc i ⊢ srvDurInv γ rc i := by
  iintro #H
  ihave #H2 := isRaft_cells r γ rc i $$ H
  unfold raftCells
  icases H2 with ⟨-, -, #H3, -⟩; iexact H3

theorem isRaft_stateCell : isRaft r γ rc i ⊢ stateCell r rc := by
  iintro #H
  ihave #H2 := isRaft_cells r γ rc i $$ H
  unfold raftCells
  icases H2 with ⟨-, -, -, #H3, -⟩; iexact H3

theorem isRaft_appliedCell : isRaft r γ rc i ⊢ appliedCell r rc := by
  iintro #H
  ihave #H2 := isRaft_cells r γ rc i $$ H
  unfold raftCells
  icases H2 with ⟨-, -, -, -, #H3, -⟩; iexact H3

theorem isRaft_lastLock : isRaft r γ rc i ⊢
    sync.isMutex (r.[Raft, go!"raftState"].[raftState, go!"lastLock"]) (lastLockInv r γ rc i) := by
  iintro #H
  ihave #H2 := isRaft_locks r γ rc i $$ H
  unfold raftLocks
  icases H2 with ⟨#H3, -⟩; iexact H3

theorem isRaft_rg : isRaft r γ rc i ⊢ rgOk r := by
  iintro #H
  ihave #H2 := isRaft_locks r γ rc i $$ H
  unfold raftLocks
  icases H2 with ⟨-, -, -, -, #H3⟩; iexact H3

theorem isRaft_applyCh : isRaft r γ rc i ⊢
    ∃ (ch : Loc) (γa : ChanNames), r.[Raft, go!"applyCh"] ↦□ ch ∗
      isChanBag (V := Loc) γa ch (applyP γ rc i) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨⟨%ch, #Hch, %γa, #Hb⟩, -⟩
  iexists ch, γa; iframe #

theorem isRaft_fsmCh : isRaft r γ rc i ⊢
    ∃ ch : Loc, r.[Raft, go!"fsmMutateCh"] ↦□ ch ∗
      isSpsc (V := GoInterface) rc.names.fsmCh ch (fsmP γ rc i) (fun _ => iprop(False)) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, ⟨%ch, #Hch, #Hb⟩, -⟩
  iexists ch; iframe #

theorem isRaft_shutdownCh : isRaft r γ rc i ⊢ deadField Unit r go!"shutdownCh" := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, -, -, -, -, #H3, -⟩; iexact H3

/-- (stage 2) `verifyCh`: a bag of verify futures (`verifyP`). -/
theorem isRaft_verifyCh : isRaft r γ rc i ⊢
    ∃ (vch : Loc) (γv : ChanNames), r.[Raft, go!"verifyCh"] ↦□ vch ∗
      isChanBag (V := Loc) γv vch (verifyP γ rc i vch) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, ⟨%vch, #Hch, %γv, #Hb⟩, -⟩
  iexists vch, γv; iframe #

/-- (stage 2) `leadershipTransferCh`: a bag of leadership transfer futures (`ltfP`). -/
theorem isRaft_ltCh : isRaft r γ rc i ⊢
    ∃ (lch : Loc) (γt : ChanNames), r.[Raft, go!"leadershipTransferCh"] ↦□ lch ∗
      isChanBag (V := Loc) γt lch (ltfP γ i) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, ⟨%lch, #Hch, %γt, #Hb⟩, -⟩
  iexists lch, γt; iframe #

/-- (stage 3) `fsmSnapshotCh`: a bag of snapshot requests. -/
theorem isRaft_fsmSnapshotCh : isRaft r γ rc i ⊢
    ∃ (ch : Loc) (γs : ChanNames), r.[Raft, go!"fsmSnapshotCh"] ↦□ ch ∗
      isChanBag (V := Loc) γs ch (snapReqP γ rc) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, ⟨%ch, #Hch, %γs, #Hb⟩, -⟩
  iexists ch, γs; iframe #

/-- (stage 3) `userSnapshotCh`: a bag of user snapshot requests. -/
theorem isRaft_userSnapshotCh : isRaft r γ rc i ⊢
    ∃ (ch : Loc) (γu : ChanNames), r.[Raft, go!"userSnapshotCh"] ↦□ ch ∗
      isChanBag (V := Loc) γu ch userSnapP := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, -, ⟨%ch, #Hch, %γu, #Hb⟩, -⟩
  iexists ch, γu; iframe #

/-- (stage 3) `configurationsCh`: a bag of configurations requests. -/
theorem isRaft_configurationsCh : isRaft r γ rc i ⊢
    ∃ (ch : Loc) (γq : ChanNames), r.[Raft, go!"configurationsCh"] ↦□ ch ∗
      isChanBag (V := Loc) γq ch (cfgReqP γ rc i) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, -, -, ⟨%ch, #Hch, %γq, #Hb⟩, -⟩
  iexists ch, γq; iframe #

/-- (stage 4) `configurationChangeCh`: a bag of configuration change futures (`ccfP`). -/
theorem isRaft_configurationChangeCh : isRaft r γ rc i ⊢
    ∃ (ch : Loc) (γq : ChanNames), r.[Raft, go!"configurationChangeCh"] ↦□ ch ∗
      isChanBag (V := Loc) γq ch (ccfP γ) := by
  iintro #H
  ihave #H2 := isRaft_chans r γ rc i $$ H
  unfold raftChans
  icases H2 with ⟨-, -, -, -, -, -, -, -, ⟨%ch, #Hch, %γq, #Hb⟩, -⟩
  iexists ch, γq; iframe #

end isRaft

/-! ## Configurations (stage 4) -/

/-- (stage 4) The voters of the configuration at index `p` of `L` (`proto.cfgAtC`, decoded with
the protocol's `γ.cv = cfgDec γ.srvs`) are the voters of the Go value `c` there (`cfgAtIs`): what
`quorumSize`, `hasVote`, `electSelf`, `checkLeaderLease` and the commitment count. -/
theorem cfgAtIs_voters (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) (hcv : γ.cv = cfgDec γ.srvs) :
    cfgAtIs (GF := GF) γ L p c ⊢
      ∃ ss : List Server, c.Servers' ↦*□ ss ∗
        ⌜cfgAtC γ.cv L p = srvVoters ss ∧ (p = 0 → ss = []) ∧ (1 ≤ p → srvsOk γ ss)⌝ := by
  unfold cfgAtIs cfgVal
  iintro (⟨%hp, #Hs⟩ | ⟨%ss, %e, ⟨#Hs, %hok⟩, %h⟩)
  · subst hp; iexists []; iframe #; ipureintro
    refine ⟨?_, fun _ => rfl, fun h => by omega⟩
    simp [cfgAtC, srvVoters]
  · obtain ⟨h1, he, -, hd⟩ := h
    iexists ss; iframe #; ipureintro
    refine ⟨?_, fun h0 => by omega, fun _ => hok⟩
    simp only [cfgAtC, he, hd, hcv]; exact cfgDec_encode _ _ hok

/-- (stage 4) The latest configuration of a log `L` (at `lastCfgIdx L`): its servers' IDs are
`cfgIdsOf L` (the replication goroutines a leader with log `L` runs). -/
theorem cfgAtIs_ids (γ : GNames) (L : RLog) (c : Configuration) :
    cfgAtIs (GF := GF) γ L (lastCfgIdx L) c ⊢
      ∃ ss : List Server, c.Servers' ↦*□ ss ∗ ⌜srvIds ss = cfgIdsOf γ.srvs L⌝ := by
  unfold cfgAtIs cfgVal
  iintro (⟨%hp, #Hs⟩ | ⟨%ss, %e, ⟨#Hs, %hok⟩, %h⟩)
  · iexists []; iframe #; ipureintro
    simp [cfgIdsOf, hp, srvIds]
  · obtain ⟨h1, he, -, hd⟩ := h
    iexists ss; iframe #; ipureintro
    simp only [cfgIdsOf, he, hd]; rw [cfgServers_encode _ _ hok]

/-- (stage 4) A valid configuration is an optional one (the latest configuration cell's). -/
theorem cfgOpt_of_cfgAtIs (γ : GNames) (L : RLog) (p : Nat) (c : Configuration) :
    cfgAtIs (GF := GF) γ L p c ⊢ cfgOpt γ c := by
  unfold cfgAtIs cfgVal cfgOpt
  iintro (⟨%hp, #Hs⟩ | ⟨%ss, %e, ⟨#Hs, %hok⟩, %h⟩)
  · iexists []; iframe #; ipureintro; exact Or.inl rfl
  · iexists ss; iframe #; ipureintro; exact Or.inr hok

/-! ## Errors -/

theorem pkgGlobals_of_init :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ pkgGlobals (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft

theorem RaftErr.mem_all (c : RaftErr) : c ∈ RaftErr.all := by
  cases c <;> simp [RaftErr.all]

theorem errVals_elem (f : RaftErr → GoInterface) (c : RaftErr) :
    errVals (GF := GF) f ⊢ globalAddr c.var ↦□ f c ∗ errors.newVar c.var c.msg := by
  unfold errVals
  iintro ⟨-, #H⟩
  iapply (BigSepL.bigSepL_mem (RaftErr.mem_all c)) $$ H

theorem isRaftErr_of_init (c : RaftErr) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ ∃ e, isRaftErr c e := by
  iintro #H
  ihave #Hg := pkgGlobals_of_init $$ H
  unfold pkgGlobals
  icases Hg with ⟨⟨%f, #Hf⟩, -⟩
  iexists f c
  unfold isRaftErr
  iexists f; iframe #; ipureintro; rfl

/-- Each error variable holds its `errors.New` error (e.g. `ErrLogNotFound`, which the
`InmemStore` proofs need as `errLogNotFoundOk`, `errLogNotFoundOk_of_newVar`). -/
theorem newVar_of_init (c : RaftErr) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢ errors.newVar (GF := GF) c.var c.msg := by
  iintro #H
  ihave #Hg := pkgGlobals_of_init $$ H
  unfold pkgGlobals
  icases Hg with ⟨⟨%f, #Hf⟩, -⟩
  icases errVals_elem f c $$ Hf with ⟨-, #Hn⟩
  iexact Hn

theorem isRaftErr_agree (c : RaftErr) (e1 e2 : GoInterface) :
    isRaftErr (GF := GF) c e1 ∗ isRaftErr c e2 ⊢ ⌜e1 = e2⌝ := by
  unfold isRaftErr
  iintro ⟨⟨%f1, #H1, %h1⟩, ⟨%f2, #H2, %h2⟩⟩
  icases errVals_elem f1 c $$ H1 with ⟨#P1, -⟩
  icases errVals_elem f2 c $$ H2 with ⟨#P2, -⟩
  icombine P1 P2 gives %h
  ipureintro; subst h1 h2; exact h

theorem isRaftErr_ne (c1 c2 : RaftErr) (e1 e2 : GoInterface) (h : c1 ≠ c2) :
    isRaftErr (GF := GF) c1 e1 ∗ isRaftErr c2 e2 ⊢ ⌜e1 ≠ e2⌝ := by
  unfold isRaftErr
  iintro ⟨⟨%f1, #H1, %h1⟩, ⟨%f2, #H2, %h2⟩⟩
  ihave #HH := H1
  iunfold errVals at HH
  icases HH with ⟨%hinj, -⟩
  icases errVals_elem f1 c2 $$ H1 with ⟨#P1, -⟩
  icases errVals_elem f2 c2 $$ H2 with ⟨#P2, -⟩
  icombine P1 P2 gives %hag
  ipureintro; subst h1 h2; rw [← hag]
  exact fun e => h (hinj e)

theorem isRaftErr_nonnil (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢ ⌜e ≠ interface.nil⌝ := by
  unfold isRaftErr
  iintro ⟨%f, #H, %h⟩
  icases errVals_elem f c $$ H with ⟨#P, #Hn⟩
  unfold errors.newVar
  icases Hn with ⟨%x, #Px, -⟩
  icombine P Px gives %h'
  ipureintro; subst h; rw [h']
  simp [interface.mkOk]

/-- The global variable holds the value (what a client comparing `err == raft.ErrX` loads). -/
theorem isRaftErr_global (c : RaftErr) (e : GoInterface) :
    isRaftErr (GF := GF) c e ⊢ globalAddr c.var ↦□ e := by
  unfold isRaftErr
  iintro ⟨%f, #H, %h⟩
  icases errVals_elem f c $$ H with ⟨#P, -⟩
  subst h; iexact P

/-! ## Observers -/

theorem obsArg_other (γ : GNames) (i : SID) (s : SState) (d : GoInterface) (h : d ≠ leaderObs)
    (h2 : ∀ v, d = interface.mkOk RaftState.ty v → ∃ st : w32, v = #st) :
    ⊢ obsArg (GF := GF) γ i s d := by
  unfold obsArg
  rw [if_neg h]
  ipureintro; exact h2

theorem obsArg_leader (γ : GNames) (i : SID) (s : SState) :
    obsArg (GF := GF) γ i s leaderObs ⊣⊢ leaderIs γ s.term i := by
  unfold obsArg
  rw [if_pos rfl]
  exact ⟨.rfl, .rfl⟩

/-! ## The FSM batch channel -/

theorem batchEnd_agree (rc : RCtx GF) (n k1 k2 : Nat) :
    batchEnd rc n k1 ∗ batchEnd rc n k2 ⊢ ⌜k1 = k2⌝ := by
  unfold batchEnd
  iintro ⟨#H1, #H2⟩
  iapply ghostMapElem_agree n rc.names.batch _ _ k1 k2 $$ H1 H2

/-! ## The client's side of a future -/

/-- `f.Error()` on the `ApplyFuture` interface value returned by `Apply` (dispatching to
`errorFuture.Error` or `deferError.Error` through `*logFuture`). The two methods' specs
(`deferError.Error.spec`, `errorFuture.Error.spec`, stated inline: their Spec files import this
one) are hypotheses. -/
theorem wp_future_Error
    (wp_dErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait (f.[logFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_eErr : ∀ (e : GoInterface),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
        (App (Val (errorFuture.mk e @!! errorFuture.ty @!! go!"Error")) (Val #()))
      {{ RET #e; True }})
    (γ : GNames) (rc : RCtx GF) (x : GoInterfaceOk) (d : List w8) (n : Nat) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       futureOwn γ rc (GoInterface.ok x) d n }}
      (App (Val #(methods x.ty go!"Error" x.v)) (Val #()))
    {{ (err : GoInterface), RET #err; futDone γ rc (GoInterface.ok x) d n err }} := by
  unfold futureOwn
  iintro %Φ ⟨#Hpkg, Hfut⟩ HΦ
  icases Hfut with (⟨%e, %hfi, He, Htok⟩ | ⟨%f, %hfi, Hw⟩)
  · obtain ⟨ty, v⟩ := x
    cases hfi
    iapply (wp_eErr e) $$ %Φ Hpkg
    inext; iintro -
    iapply HΦ
    unfold futDone
    ileft; iframe
  · obtain ⟨ty, v⟩ := x
    cases hfi
    iapply (wp_dErr f (futQ γ rc f d n)) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ
    unfold futQ futDone
    icases Hq with (⟨Herr, Htok⟩ | ⟨%he, %k, %e, %r, #Hc, %hk, Hr, Hf⟩ | Hl)
    · ileft; iframe
      icases Herr with (H | H)
      · ileft; iexact H
      · iright; ileft; iexact H
    · iright; ileft; isplitr
      · ipureintro; exact he
      iexists f, k, e, r; iframe #; iframe; ipureintro; exact ⟨rfl, hk⟩
    · iright; iright; iexact Hl

/-- (stage 2) A verify future's registrations agree (a voted future's `T`, `sv` are those its
leader registered: leaderLoop's quorum case ties the votes to its own term and the client's
snapshot). -/
theorem vregIs_agree (rc : RCtx GF) (v : Loc) (T1 T2 : Nat) (sv1 sv2 : Snap) :
    vregIs rc v T1 sv1 ∗ vregIs rc v T2 sv2 ⊢ ⌜T1 = T2 ∧ sv1 = sv2⌝ := by
  unfold vregIs
  iintro ⟨#H1, #H2⟩
  ihave %H := ghostMapElem_agree v rc.names.vreg _ _ (T1, sv1) (T2, sv2) $$ H1 H2
  ipureintro
  exact Prod.mk.inj H

/-- (stage 2) `fi.Error()` on a client's `Future` interface value (`futWait`: `Barrier`'s,
`VerifyLeader`'s, `LeadershipTransfer`'s; stage 4: the configuration changes'; dispatching to
`errorFuture.Error` or `deferError.Error` promoted through `*logFuture`, `*verifyFuture`,
`*leadershipTransferFuture`, `*userSnapshotFuture`, `*configurationChangeFuture`): the answer `Q`. The
methods' specs (`deferError.Error.spec`, `errorFuture.Error.spec`) are hypotheses. -/
theorem wp_futWait_Error
    (wp_dErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait (f.[logFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_vErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait (f.[verifyFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_tErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait (f.[leadershipTransferFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_uErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait (f.[userSnapshotFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType userSnapshotFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_cErr : ∀ (f : Loc) (Q : GoInterface → IProp GF),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         deferWait ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]) Q }}
        (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"Error")) (Val #()))
      {{ (err : GoInterface), RET #err; Q err }})
    (wp_eErr : ∀ (e : GoInterface),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
        (App (Val (errorFuture.mk e @!! errorFuture.ty @!! go!"Error")) (Val #()))
      {{ RET #e; True }})
    (x : GoInterfaceOk) (Q : GoInterface → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ futWait (GoInterface.ok x) Q }}
      (App (Val #(methods x.ty go!"Error" x.v)) (Val #()))
    {{ (err : GoInterface), RET #err; Q err }} := by
  unfold futWait
  iintro %Φ ⟨#Hpkg, Hfut⟩ HΦ
  obtain ⟨ty, v⟩ := x
  icases Hfut with (⟨%e, %hfi, He⟩ | ⟨%f, %hfi, Hw⟩ | ⟨%f, %hfi, Hw⟩ | ⟨%f, %hfi, Hw⟩ | ⟨%f, %hfi, Hw⟩ |
    ⟨%f, %hfi, Hw⟩)
  · cases hfi
    iapply (wp_eErr e) $$ %Φ Hpkg
    inext; iintro -
    iapply HΦ $$ He
  · cases hfi
    iapply (wp_dErr f Q) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ $$ Hq
  · cases hfi
    iapply (wp_vErr f Q) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ $$ Hq
  · cases hfi
    iapply (wp_tErr f Q) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ $$ Hq
  · cases hfi
    iapply (wp_uErr f Q) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ $$ Hq
  · cases hfi
    iapply (wp_cErr f Q) $$ %Φ [$Hpkg $Hw]
    inext; iintro %err Hq
    iapply HΦ $$ Hq

/-- `f.Response()` on the future after `Error()` returned `nil` (`logFuture.Response.spec`,
stated inline, is the hypothesis). -/
theorem wp_future_Response
    (wp_lResp : ∀ (f : Loc) (r : GoInterface) (dq : DFrac),
      {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
         f.[logFuture, go!"response"] ↦{dq} r }}
        (App (Val (f @!! go.GoType.PointerType logFuture.ty @!! go!"Response")) (Val #()))
      {{ RET #r; f.[logFuture, go!"response"] ↦{dq} r }})
    (f : Loc) (r : GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       f.[logFuture, go!"response"] ↦{dq} r }}
      (App (Val #(methods (go.GoType.PointerType logFuture.ty) go!"Response" #f)) (Val #()))
    {{ RET #r; f.[logFuture, go!"response"] ↦{dq} r }} :=
  wp_lResp f r dq

end laws

end github_com.hashicorp.raft

end Perennial
