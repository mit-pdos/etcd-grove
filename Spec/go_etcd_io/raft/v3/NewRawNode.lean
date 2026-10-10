/- Lean-first (no Rocq counterpart).

## `NewRawNode` (rawnode.go:51), a fresh node

`NewRawNode(config)` is `newRaft(config)` in a new `RawNode` that records the config's
`AsyncStorageWrites` and the node's initial `SoftState` and `HardState`. Specified for a
node of a new cluster: an empty storage (no entries, no `HardState`, nothing applied),
synchronous storage writes, and the ghost state of the protocol's initial state, which
`ownRaftGhost_alloc` (`Protocol/Facts.lean`) hands out for every voter of the cluster with
`isCommitted γ []`. The premises on the `Config` and the storage are `newRaft`'s
(`Spec/newRaft.lean`).

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Spec.go_etcd_io.raft.v3.newRaft
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

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
theorem newRaft_post_init (hs : raftpb.HardState) (s : NState) :
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
    NStateRel s initPState := by
  intro ⟨HT, HV, _⟩ ⟨Hwf, Ht, Hv, Hl, Hr, Hvs, Ho⟩ Hp Hse Hue Hc
  refine ⟨?_, Hwf⟩
  simp [toPState, initPState, Ht, Hv, HT, HV, Hl, Hr, Hvs, Ho, Hp, Hse, Hue, Hc, proleRole]

end newRaft_post

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- See the file header. -/
abbrev NewRawNode.spec : Prop :=
  ∀ (γ : RaftNames) (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (σ : StorState)
    (hs : raftpb.HardState) (cs : raftpb.ConfState)
    (voters : List w64) (dqv : DFrac),
  -- the Config, as for `newRaft`
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.CheckQuorum' = false →
  cv.DisableProposalForwarding' = false →
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
  voters ≠ [] → voters.Nodup → W64 0 ∉ voters → (voters.length : Int) ≤ 2 ^ 62 →
  cs.VotersOutgoing'.len = W64 0 →
  cs.Learners'.len = W64 0 →
  cs.LearnersNext'.len = W64 0 →
  cs.AutoLeave' = false →
  γ.reCfg = GMap.listToSet voters →
  cv.ID' ∈ voters →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isStorage (interface.ok si) ∗ ownStorage (interface.ok si) σ ∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID), ownStorage (interface.ok si) { σ with ss := ss' } -∗
           (ownStorage (interface.ok si) { σ with ss := ss' } -∗
            cs.Voters' ↦*{dqv} voters -∗
            Φ (PairV (PairV #hs #cs) #interface.nil)) -∗
           WP (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #())) {{ Φ }}) ∗
      "Hghost" ∷ ownRaftGhost γ cv.ID' initPState ∗
      "#Hcommitted" ∷ isCommitted γ [] }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      "Hrn" ∷ ownRawNode γ rn cv.ID'
        { delivered := [], unpersisted := [], steps := [], term := W64 0,
          storage := interface.ok si } ∗
      "%Herr" ∷ ⌜err = interface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
