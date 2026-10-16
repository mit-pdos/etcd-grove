/- Lean-first (no Rocq counterpart).

## `NewRawNode` (rawnode.go:51), a fresh node

`NewRawNode(config)` is `newRaft(config)` in a new `RawNode` that records the config's
`AsyncStorageWrites` and the node's initial `SoftState` and `HardState`. Specified for a
node of a new cluster: an empty storage (no entries, no `HardState`, nothing applied),
synchronous storage writes, and the ghost state of the protocol's initial state, which
`ownRaftGhost_alloc` (`Protocol/Facts.lean`) hands out for every voter of the cluster with
`isCommitted γ []`. The premises on the `Config` and the storage are `newRaft`'s
(`Spec/newRaft.lean`).

raft v3.7 (2026-10-16, stage R5): the storage's `InitialState` premise is `newRaft`'s (stage R4,
D7: two pointers, the hard state `hsOpt hp hs` and the conf state `csPts cs □ csm true`,
`ownStorage` back at once; until then the Goose values `hs`, `cs` and `cs.Voters` lent at `dqv`);
the conf state is the record `csm`, its voters `csm.Voters'`. `NewRawNode` sets `prevHardSt :=
r.hardState()`, a fresh read-only hard state (`ownRawNode`'s `Hhard`).

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvRawnode
public import Raft37.Spec.go_etcd_io.raft.v3.newRaft
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.Facts
-- `rinit` (2026-10-14, reconfiguration stage B7 part 2)
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section newRaft_post
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- `newRaft`'s postcondition, on a storage with no persisted `HardState` and an empty
log, is the protocol's initial state. (Since 2026-10-01 the protocol state has the log,
and `initPState`'s is empty: a node starting from a storage that already holds entries
is not at `initPState`, and `ownRaftGhost_alloc` does not cover it -- its entries would
need `isEntry`s.) -/
theorem newRaft_post_init (hs : HardStateM) (s : NState) :
    HsEmpty hs →
    (NStateWf s ∧
     s.term = hs.Term' ∧
     s.vote = hs.Vote' ∧
     s.lead = W64 0 ∧ s.role = .follower ∧
     s.votes = ∅ ∧ s.outbox = []) →
    s.logst.prev = entryID.mk (W64 0) (W64 0) →
    s.logst.sents = [] →
    s.logst.uents = [] →
    s.logst.committed = W64 0 →
    s.rd.states = [] → s.rd.pend = [] →
    NStateRel s initPState := by
  intro ⟨HT, HV, _⟩ ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ Hp Hse Hue Hc Hst Hpd
  refine ⟨?_, Hwf⟩
  simp [toPState, initPState, Ht, Hv, HT, HV, Hl, Hr, Hvs, Ho, Hp, Hse, Hue, Hc, proleRole, rdNL]
  cases h : s.rd
  simp_all

end newRaft_post

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The ghost state a fresh node starts from, in the mode `md` (2026-10-14, reconfiguration stage
B7 part 2): statically the protocol's initial state (`ownRaftGhost_alloc`); dynamically the
dynamic model's (`raft_dyn_alloc`, at `rinit c0`), the initial configuration `c0` the voters `V`
of the persisted `ConfState`, with no learner. -/
def rnInit (γ : RaftNames) (md : RNMode) (id : w64) (V : GSet w64) : IProp GF :=
  match md with
  | .static => ownRaftGhost γ id initPState
  | .dyn dec c0 h0 _ => iprop(⌜γ.dyn = some (DynCfg.ofFold dec c0 h0) ∧ c0 = cfgState V ∅⌝ ∗
      ownRaftGhostR γ dec c0 id (rinit c0))

/-- See the file header. -/
abbrev NewRawNode.spec : Prop :=
  ∀ (γ : RaftNames) (md : RNMode) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM),
  -- the Config, as for `newRaft`
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.CheckQuorum' = false →
  cv.DisableProposalForwarding' = false →
  -- `ReadOnlySafe` (2026-10-12)
  cv.ReadOnlyOption' = W64 0 →
  -- conf-change validation on (2026-10-13; `newRaft`'s premise)
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  -- synchronous storage writes, nothing applied
  cv.AsyncStorageWrites' = false →
  -- pre-vote off (2026-10-10): pre-vote is an optimization, out of scope (`ownRawNode`)
  cv.PreVote' = false →
  cv.Applied' = W64 0 →
  -- an empty storage: no entries, no `HardState`
  σ.prev = entryID.mk (W64 0) (W64 0) →
  σ.ents = [] →
  (uint.Z σ.ss.index' = 0 ∨ σ.ss = σ.prev) →
  σ.pend = [] →
  HsEmpty hs →
  -- the persisted ConfState: voters only, this node among them, and the cluster's
  -- (2026-10-16, stage R5: the record `csm`, as `newRaft`'s; until then the Goose value `cs`
  -- and the list `voters` its slice held)
  csm.Voters' ≠ [] → csm.Voters'.Nodup → W64 0 ∉ csm.Voters' →
  (csm.Voters'.length : Int) ≤ 2 ^ 62 →
  csm.VotersOutgoing' = [] →
  csm.Learners' = [] →
  csm.LearnersNext' = [] →
  csm.AutoLeave' = false →
  γ.reCfg = GMap.listToSet csm.Voters' →
  cv.ID' ∈ csm.Voters' →
  -- (2026-10-14) the dynamic mode with `StepDownOnRemoval` (a removed leader steps down)
  (md.isDyn = true → cv.StepDownOnRemoval' = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      -- (2026-10-16, stage R5) `InitialState` in `newRaft`'s shape (stage R4, D7): the hard state
      -- `hsOpt hp hs` and the conf state read-only for good, `ownStorage` back at once
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc), ownStorage (interface.ok si) { σ with ss := ss' } -∗ hsOpt hp hs -∗
            csPts cs DFrac.discard csm true -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      "Hghost" ∷ rnInit γ md cv.ID' (GMap.listToSet csm.Voters') ∗
      "#Hcommitted" ∷ isCommitted γ [] }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      "Hrn" ∷ ownRawNode γ rn cv.ID'
        { delivered := [], unpersisted := [], steps := [], term := W64 0,
          storage := interface.ok si, mode := md,
          cfg := cfgState (GMap.listToSet csm.Voters') ∅ } ∗
      "%Herr" ∷ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
