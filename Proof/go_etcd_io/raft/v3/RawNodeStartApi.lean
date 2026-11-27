/-
Lean-first (antithesis parity B1 phase 2, #33). **`NewRawNode` restarting into the sealed node at a
mode**: `NewRawNode.restartAtApiSpec`, `NewRawNode.restartAtSpec`'s statement (`RawNodeStart.lean`)
over the sealed `rawNode γ md …` (`RawNodeApi.lean`), at any mode `md` without snapshots and without
configuration changes. The scope's premises are `RestartScopeOk … md` itself, the storage's
`storCapF … 0` unguarded (snapshots off), and the ghost prefix below the log's boundary is empty (the
boundary is `base0` without snapshots), so the post names the restarted state `restartR … []`.
Also the restart's `restartR` and `RestartScopeOk` (moved here from `RawNodeStart.lean`, unchanged, so
that this statement is in a defs module). Proved in `RawNodeApiLinked.lean` from
`NewRawNode.restartAtSpec (some md)` (`NewRawNode.wp_proofRestartAtApi`).
-/
module

public import Proof.go_etcd_io.raft.v3.RawNodeApi
public import Proof.go_etcd_io.raft.v3.RawNodeStartSpec
public import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section start_api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (antithesis parity B1) **The `RState` a node restarts at**: the restarted protocol state
`restartP`, the applied index `ap`, no pending conf index, no snapshot, the configuration `cs` at the
configuration index `a`, the ghost prefix `fp`. -/
def restartR (S : RaftState) (σ : StorContents) (ap a : Nat) (cs : CCState) (fp : List EntryM) :
    RState :=
  { p := restartP S σ.base σ.hs.Commit', applied := W64 ap, pci := W64 0, snap := false, cidx := a,
    cfg := cs, fp := fp }

/-- (antithesis parity B1) **The restart's scope premises at the mode `md`**, one per flag: pre-vote
and check-quorum off unless `md` lifts them, the node among the names' voters unless `nonVoters`,
the configuration simple over the names' voters with no learners unless `confChanges`, the log's
boundary `base0` unless `snapshots`. -/
def RestartScopeOk (γ : Cluster) (cv : Config) (σ : StorContents) (m : Membership) (md : RnMode) :
    Prop :=
  (md.prevote = false → cv.PreVote' = false) ∧ (md.cq = false → cv.CheckQuorum' = false) ∧
  (md.nonVoters = false → cv.ID' ∈ γ.raftNames.reCfg) ∧
  (md.confChanges = false → m.voters = γ.raftNames.reCfg ∧ m.votersOutgoing = ∅ ∧ m.learners = ∅) ∧
  (md.snapshots = false → σ.base = base0)

/-- **`NewRawNode` restarting into `rawNode` at the mode `md`** (snapshots and configuration changes
off): `NewRawNode.restartAtSpec (some md)`'s text over the sealed node, the scope premises
`RestartScopeOk … md`, the storage never compacted (`storCapF … 0`), the post's node at the
restarted state `restartR` with no ghost prefix. -/
abbrev NewRawNode.restartAtApiSpec : Prop :=
  ∀ (md : RnMode), md.snapshots = false → md.confChanges = false → md.async = false →
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership) (S : RaftState)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  γ.bootLen ≤ σ.last →
  confStateIs csm m →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  StorageHolds S σ →
  RestartScopeOk γ cv σ m md →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' S ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F SV ∗
      storCapF (interface.ok si) 0 }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (l : List EntryM) (sn : StorNames) (g : Nat) (K : GName),
        rawNode γ.raftNames md rn cv.ID'
          { rawNodeRestarted γ l (interface.ok si) sn σ.hs S m a with k := cfgK cv }
          (restartR S σ (max σ.b (uint.nat cv.Applied')) a (ApiImpl.stOf m) []) []
          (σ.b + σ.ents.length) ∗
        isCommitted γ.raftNames l ∗
        ⌜l.length = max σ.b (uint.nat cv.Applied') ∧ l.drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' S ∗ F K }}


/-- (antithesis parity B2, design §7 Q8) **A restarted node has no read request pending and no read
state** (`restartP` is `initPState`'s with the durable fields: `newRaft`'s `readOnly` and
`readStates` are fresh). -/
theorem restartR_rd (S : RaftState) (σ : StorContents) (ap a : Nat) (cs : CCState)
    (fp : List EntryM) :
    (restartR S σ ap a cs fp).p.rd.pend = [] ∧ (restartR S σ ap a cs fp).p.rd.states = [] :=
  ⟨rfl, rfl⟩

/-- (antithesis parity B2, design §4 "The vacate law": `durContents`) **The storage contents of a
durable state**: what a storage refilled from the client's durable state `S` holds (the harness's
durable wrapper, kvdurable's pattern): `S`'s term, vote and commit as the hard state, no snapshot,
`S`'s base and entries. -/
def durContents (S : RaftState) : StorContents :=
  { hs := HardStateM.mk S.term S.vote S.commit, snap := none, base := S.base, ents := S.ents }

/-- (antithesis parity B2; a statement, proved in round 2) **A durable state's own contents hold it**
(`StorageHolds`, the restart's premise), given its base and the commit of its last log-writing batch
at most its commit. -/
abbrev StorageHolds_durContents.law : Prop :=
  ∀ S : RaftState, uint.nat S.base.index' ≤ uint.nat S.commit →
    uint.nat S.wcommit ≤ uint.nat S.commit → StorageHolds S (durContents S)

/-- (antithesis parity B2, design §4 "The vacate law"; a statement, proved in round 2 from
`raft_stop`) **Dropping a `RawNode` gives its id's vacancy back** (`node.Stop`'s counterpart for an
in-process restart; no `crashed`, so not `nodeCrash`): the node, at any state and mode, with the whole
of its generation's view (`genView … 1 g`: the client's, as no `run` goroutine shares it) gives the
vacancy armed at the same arm `x` (`raft_stop`: the generation bumped, the volatile half's pieces back
in the arm's crash invariant). The durable state stays the client's (`raftState`, untouched): a batch
handed out and not entered is discarded (the binding's undo of an unmade write). A `Ready`'s `Henter`
taken before is dead after: it needs `genView … g`, and the generation is past `g` for good. -/
abbrev rawNode_vacate.law : Prop :=
  ∀ (md : RnMode) (γ : Cluster) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg)
    (ip : Nat) (x : CrashNames) (g : Nat) (E : CoPset),
    ↑(raftN γ.raftNames) ⊆ E →
    ⊢ notCrashed -∗ rawNode (GF := GF) γ.raftNames md rn id rs r qs ip -∗
      genView γ.raftNames id x 1 g ={E}=∗ notCrashed ∗ nodeVacantA γ id x

/-- (antithesis parity B2, design §4's `NewRawNode` restart row; a statement, proved in round 2)
**`NewRawNode` restarting into `rawNode` at a mode with or without async writes**:
`NewRawNode.restartAtApiSpec`'s text but for the `Config`'s `AsyncStorageWrites`, which is the mode's
`async` flag (until round 2, `restartAtApiSpec` covers `false` only). The restarted node has no read
request pending (`restartR_rd_pend`, design §7 Q8). -/
abbrev NewRawNode.restartAtApiSpecAsync : Prop :=
  ∀ (md : RnMode), md.snapshots = false → md.confChanges = false →
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorContents) (csm : ConfStateM) (a : Nat) (m : Membership) (S : RaftState)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = md.async →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  (uint.nat cv.Applied' = 0 ∨ σ.b ≤ uint.nat cv.Applied' ∧ uint.nat cv.Applied' ≤ σ.commit) →
  max σ.b (uint.nat cv.Applied') ≤ a → a ≤ σ.commit →
  γ.bootLen ≤ σ.last →
  confStateIs csm m →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  StorageHolds S σ →
  RestartScopeOk γ cv σ m md →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' S ∗
      confAt γ a m ∗
      restartStorage γ (interface.ok si) σ csm (uint.nat cv.Applied') F SV ∗
      storCapF (interface.ok si) 0 }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (l : List EntryM) (sn : StorNames) (g : Nat) (K : GName),
        rawNode γ.raftNames md rn cv.ID'
          { rawNodeRestarted γ l (interface.ok si) sn σ.hs S m a with k := cfgK cv }
          (restartR S σ (max σ.b (uint.nat cv.Applied')) a (ApiImpl.stOf m) []) []
          (σ.b + σ.ents.length) ∗
        isCommitted γ.raftNames l ∗
        ⌜l.length = max σ.b (uint.nat cv.Applied') ∧ l.drop σ.b = σ.ents.take (l.length - σ.b)⌝ ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' S ∗ F K }}

end start_api

end EtcdGrove
end Perennial
