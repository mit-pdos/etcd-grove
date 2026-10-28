/-
The protocol-level results of the dynamic model (2026-10-14, reconfiguration stage B5): safety
of raft with configurations changing by applied conf entries (`StepR` at `AdmFold dec c0`),
proved with the ghost argument (`notes/reconfiguration-safety.md`), at the model level.

**A model theorem, not yet reached from Go**: the code produces `Step` witnesses at a static
configuration (`raft__Step.lean`); stage B7 connects it to `StepR` and to this ghost state.

* `raft_dyn_alloc`: the dynamic ghost state allocated for nodes starting from `c0` with an empty
  log (`ownRaftGhostR` of `rinit c0`).
* `ownRaftGhostR_stepR` (`RefinementDyn.lean`): every `StepR` step keeps it, given the messages
  it consumed (each `isMessage`, what every sent message carries) and the records of the
  snapshot prefixes it may restore.
* `raft_dyn_committed_agree` (**log agreement / state machine safety**): the committed prefixes
  of any two nodes are prefixes of one another -- each is a prefix of the one global committed
  log (`isCommitted`).
* `raft_dyn_election_safety`: two leaders of a term are one node.
* `raft_dyn_read_states`, `raft_dyn_read_index` (2026-10-14, stage B6, **the read-index
  guarantee**): every `ReadState` a node holds (hands out at `StepR.takeReads`) is
  `readStateRaw`, so the committed prefix of any node whose commit index reaches its index
  extends the committed log the request was created knowing.

Assumptions (model restrictions, `notes/STATUS.md`, "Reconfiguration, stage B5"): A1
(`ApplyConfChange` for every committed conf entry, in order, once, before the `Advance` that
acknowledges it: `StepR.advance`/`applyConf`); A3 (a snapshot's configuration is its prefix's
fold, `AdmFold`, and the restored prefix is the committed one: its records, `S`); fresh nodes
from one `c0` with `CfgOk c0` and an empty log, no crash-restart (so atomic persistence is moot);
no panic (`cfgFold` defined on the applied prefixes: `RInv`); `AppCommitEq` (an `MsgApp` carries the sender's
commit index, as Go's `sendAppend` does). (Until 2026-10-14 also: the single-voter read-index
shortcut not modelled; it is now `StepR.readSingle`/`readReleaseSingle`, the fixed raft's,
`issues/raft-readindex-singleton-stale.md`.)
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- A fresh node of the dynamic model: the initial protocol state, configuration `c0`, nothing
applied. -/
def rinit (c0 : CCState) : RState :=
  { p := initPState, applied := W64 0, pci := W64 0, snap := false, cidx := 0, cfg := c0, fp := [] }

theorem RInv_rinit (dec : CCDec) (c0 : CCState) : RInv dec c0 (rinit c0) :=
  RInv_init dec c0 (rinit c0) [] rfl rfl rfl (by simp) rfl rfl rfl rfl rfl (by rfl)

/-- The dynamic ghost state of the nodes `ids`, allocated (with the commit invariant). -/
theorem raft_dyn_alloc (E : CoPset) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (ids : GSet w64)
    -- (2026-10-15, stage N) the conf-change bytes the cluster admits
    (ccOk : w32 → List w8 → Prop) (C : RaftNames → IProp GF) :
    W64 0 ∉ ids →
    ⊢ allocClient E c0.cfg.incoming (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) C -∗
      |={E}=> ∃ γ : RaftNames,
        ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ γ.reCCOk = ccOk ∧ γ.reCfg = c0.cfg.incoming ∧
          -- (2026-10-19, D22 S-a) leader transfer on (`RaftNames.reNoXfer`)
          γ.reNoXfer = false⌝ ∗
        raftCommitInv (GF := GF) γ ∗ C γ ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhostR γ dec c0 id (rinit c0)) ∗
        -- (2026-10-15, stage N) as `ownRaftGhost_alloc`: the empty committed log, every read
        -- credit
        isCommitted γ [] ∗ rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ := by
  intro Hnz
  iintro Hcl
  imod ownRaftGhost_alloc_gen (GF := GF) E c0.cfg.incoming ids
    (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) ccOk C h0.2.1 Hnz $$ Hcl
    with ⟨%γ, %Hγ, #Hinv, #Hc0, Hn, HC, Hcr, #Hcri⟩
  simp only [Option.isSome_some]
  imodintro
  iexists γ
  isplitr
  · ipureintro
    refine ⟨?_, Hγ.2.2.1, Hγ.1, Hγ.2.2.2⟩
    unfold RaftNames.dyn; rw [Hγ.2.1]; simp [DynCfg.all_self]
  iframe Hinv HC Hc0 Hcr Hcri
  iapply BigSepM.bigSepM_impl $$ Hn
  imodintro
  iintro %id %u %_ Hg
  unfold ownRaftGhostR
  rw [show (rinit c0).p = initPState from rfl]
  iframe Hg
  isplitr; · ipureintro; exact RInv_rinit dec c0
  isplitr
  · unfold logRecs rinit
    iapply (BigSepL.bigSepL_nil).2; iempintro
  iintro %h
  exfalso; exact absurd h (by simp [initPState])

/-- (2026-10-25, T-M M2a) A member of a new cluster after `RawNode.Bootstrap`, in the dynamic
model: the bootstrap state (`bootPState bootLog`: term `1`, the boot log committed), configuration
`c0` (the peers', which `Bootstrap` installs in the tracker), at the configuration index `0`:
nothing applied, so the application re-applies the boot entries (`ApplyConfChange`, as the
first `Ready` hands them out), each through the ordinary dynamic rule. -/
def rboot (c0 : CCState) (bootLog : List EntryM) : RState :=
  { p := bootPState bootLog, applied := W64 0, pci := W64 0, snap := false, cidx := 0, cfg := c0,
    fp := [] }

/-- `RInv` of the bootstrap state: I1 holds at the commit index, the log's end; the configuration
is the fold of no entry. -/
theorem RInv_rboot (dec : CCDec) (c0 : CCState) (bootLog : List EntryM)
    (hL : (bootLog.length : Int) < 2 ^ 64) : RInv dec c0 (rboot c0 bootLog) := by
  have hc : uint.Z (rboot c0 bootLog).p.commit = bootLog.length := by
    show uint.Z (W64 (bootLog.length : Int)) = _
    exact uint_Z_W64 _ (by omega) hL
  have hcn : uint.nat (rboot c0 bootLog).p.commit = bootLog.length := by
    have := rUnat_eq (rboot c0 bootLog).p.commit; omega
  have hfull : (rboot c0 bootLog).full = bootLog := by
    show [] ++ bootLog = bootLog; rfl
  have h0 := base0_index
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FullOk_base0
  · show uint.Z base0.index' ≤ _; rw [h0, hc]; omega
  · show _ ≤ plogLastIndexZ base0 bootLog; unfold plogLastIndexZ; rw [h0, hc]; omega
  · show uint.nat (W64 0) ≤ 0; decide
  · show 0 ≤ _; omega
  · intro h; cases h
  · intro _; show uint.Z base0.index' ≤ uint.Z (W64 0); rw [h0]; decide
  · intro h; cases h
  · intro _; show cfgFold dec c0 (([] ++ bootLog).take 0) = some c0; rfl
  · rw [hfull, hcn]
    intro k1 k2 e1 e2 hlt _ h2 _ _
    have := (List.getElem?_eq_some_iff.mp h2).1
    omega
  · intro h; cases h
  · intro h; cases h

/-- (2026-10-25, T-M M2a) **The dynamic ghost state of a new cluster**: as `raft_dyn_alloc`, but
the nodes `ids` at the bootstrap state `rboot c0 bootLog` and the committed log `bootLog` from the
start (`ownRaftGhost_alloc_core` at the boot log in the dynamic mode, whose boot conf entries need
no witness: `witsB`), in the no-snapshot and no-transfer modes `ns`, `nx` or not. -/
theorem raft_dyn_alloc_boot (E : CoPset) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (ids : GSet w64) (ccOk : w32 → List w8 → Prop) (bootLog : List EntryM)
    (C : RaftNames → IProp GF) (ns nx : Bool) :
    W64 0 ∉ ids → bootLog ≠ [] → BootWf bootLog →
    ⊢ allocClientGen E c0.cfg.incoming (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) ccOk bootLog C -∗
      |={E}=> ∃ γ : RaftNames,
        ⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ γ.reCCOk = ccOk ∧ γ.reCfg = c0.cfg.incoming ∧
          γ.reBoot = bootLog ∧ γ.reNoSnap = ns ∧ γ.reNoXfer = nx⌝ ∗
        raftCommitInv (GF := GF) γ ∗ C γ ∗
        ([∗map] id ↦ _u ∈ toMap ids, ownRaftGhostR γ dec c0 id (rboot c0 bootLog)) ∗
        isCommitted γ bootLog ∗ rdCred γ (2 ^ 64 - 2) ∗ rdCredInv γ := by
  intro Hnz Hbne Hok
  have Hlen : (bootLog.length : Int) < 2 ^ 64 := by have := Hok.1; omega
  iintro Hcl
  imod ownRaftGhost_alloc_core (GF := GF) E c0.cfg.incoming ids
    (some (DynCfg.all (DynCfg.ofFold dec c0 h0))) ccOk bootLog (W64 1) C none
    (fun _ h => by cases h) ns (fun _ => Hbne) nx (fun _ => Hbne) (fun _ _ => True) (fun _ => none)
    (nroot .@ "raft_commit") (nroot .@ "raft_snapcert") h0.2.1 Hnz Hok
    (fun _ => by rw [show uint.Z (W64 1) = 1 from rfl]; exact Int.le_refl _)
    $$ Hcl with ⟨%γ, %Hγ, #Hinv, #Hc0, Hn, HC, Hcr, #Hcri⟩
  simp only [Option.isSome_some]
  imodintro
  iexists γ
  isplitr
  · ipureintro
    refine ⟨?_, Hγ.2.2.1, Hγ.1, Hγ.2.2.2.1, Hγ.2.2.2.2.2.1, Hγ.2.2.2.2.2.2.1⟩
    unfold RaftNames.dyn; rw [Hγ.2.1]; simp [DynCfg.all_self]
  iframe Hinv HC Hc0 Hcr Hcri
  iapply BigSepM.bigSepM_impl $$ Hn
  imodintro
  iintro %id %u %_ Hg
  unfold ownRaftGhostR
  rw [show (rboot c0 bootLog).p = initPStateAt (W64 1) bootLog from rfl]
  iframe Hg
  isplitr; · ipureintro; exact RInv_rboot dec c0 bootLog Hlen
  isplitr
  · unfold logRecs rboot
    iapply (BigSepL.bigSepL_nil).2; iempintro
  iintro %h
  exfalso; exact absurd h (by simp [initPStateAt, initPState])

end ghost

end EtcdGrove
end Perennial
