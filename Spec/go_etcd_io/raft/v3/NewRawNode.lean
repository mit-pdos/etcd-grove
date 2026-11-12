/- Lean-first (no Rocq counterpart).

## `NewRawNode` (rawnode.go:51), a fresh node

`NewRawNode(config)` is `newRaft(config)` in a new `RawNode` that records the config's
`AsyncStorageWrites` and the node's initial `SoftState` and `HardState`. Specified for a
node of a new cluster: an empty storage (no entries, no `HardState`, nothing applied),
synchronous storage writes. The premises on the `Config` and the storage are `newRaft`'s
(`Spec/newRaft.lean`).

Since 2026-10-16 (stage R8b, D12) the result is the node **open** (`rawNodeFresh`,
`InvBoot.lean`: the `RawNode`'s fields, the raft struct at the conf state's voters, at a state
refining the protocol's initial state), with no ghost state involved -- `NewRawNode` knows
nothing of the cluster's ghost state -- and the conf state possibly empty (a new cluster's).
`RestartNode` closes it (`ownRawNode`, in the mode `md`, with the ghost state `rnInit` below:
statically `ownRaftGhost_alloc`'s initial state, dynamically `raft_dyn_alloc`'s); `setupNode`
hands it to `RawNode.Bootstrap`, which installs the peers. (Until then the result was
`ownRawNode` at the initial state, with `rnInit` and `isCommitted γ []` as premises, at least
one voter, this node among them.)

raft v3.7 (2026-10-16, stage R5): the storage's `InitialState` premise is `newRaft`'s (stage R4,
D7: two pointers, the hard state `hsOpt hp hs` and the conf state `csPts cs □ csm al` -- its
`AutoLeave` cell set or not, 2026-10-16, stage R6b; `true` until then --, `ownStorage` back at
once; before the retarget the Goose values `hs`, `cs` and `cs.Voters` lent at `dqv`);
the conf state is the record `csm`, its voters `csm.Voters'`. `NewRawNode` sets `prevHardSt :=
r.hardState()`, a fresh read-only hard state (`ownRawNode`'s `Hhard`).

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvRawnode
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.newRaft
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
-- `rinit` (2026-10-14, reconfiguration stage B7 part 2)
public import Proof.go_etcd_io.raft.v3.Protocol.ResultsDyn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section newRaft_post
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- (2026-10-26, raft's signature, stage 1) `rnInit` moved to `Proof.go_etcd_io.raft.v3.ApiVocab`.

/-- See the file header. (raft-final phase 1, 2026-10-29: over `newRaft`'s boot bundle, U8 v2 step 4's
decision (B); until then raft's view of an empty storage with an `InitialState` closure.) (2026-11-01,
durability stage I-6: `newRaft`'s generalized premises -- a storage holding a log from a base, a
hard state, `Applied`, any `ConfState` `Restore` accepts -- and the node open at it, `rawNodeAt`;
until then an empty storage, `rawNodeFresh`, which `rawNodeAt_fresh` gives back.) (2026-11-12, trace-check step 5) Both modes, `newRaft`'s changes; the node `rawNodeAt` at the struct `r`, with the trace mode, `s.cq`, `trNoCut` and the capability after positions 0-2 beside it. -/
abbrev NewRawNode.spec : Prop :=
  ∀ (c : Loc) (cv : Config) (lok si : GoInterfaceOk)
    (sn : StorNames) (σ : StorState)
    (hs : HardStateM) (csm : ConfStateM) (R R' : IProp GF) (cs' : CCState)
    (γ : RaftNames) (vs : List w64),
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  LogIndicesOk σ.prev σ.ents → σ.pend = [] →
  uint.nat σ.prev.index' ≤ σ.fr → σ.fr ≤ uint.nat (committedAfter σ.prev hs) →
  uint.Z σ.fl ≤ uint.Z σ.prev.index' → σ.sg ≤ uint.nat σ.prev.index' →
  σ.dt = ∅ →
  uint.Z σ.prev.index' + (σ.ents.length : Int) + 1 < 2 ^ 64 →
  AttachRec sn σ.prev σ.ents (uint.nat (committedAfter σ.prev hs))
    (max (uint.nat σ.prev.index') (uint.nat cv.Applied')) →
  (HsEmpty hs ∨ uint.Z σ.prev.index' ≤ uint.Z hs.Commit' ∧
    uint.Z hs.Commit' ≤ uint.Z σ.prev.index' + (σ.ents.length : Int)) →
  (cv.Applied' = W64 0 ∨ uint.Z σ.prev.index' ≤ uint.Z cv.Applied' ∧
    uint.Z cv.Applied' ≤ uint.Z (committedAfter σ.prev hs)) →
  restoreM csm.VotersOutgoing' csm.Voters' csm.Learners' csm.LearnersNext' csm.AutoLeave' =
    some cs' →
  (GMap.size (GMap.listToSet csm.Voters' ∪ GMap.listToSet csm.VotersOutgoing' ∪
    GMap.listToSet csm.Learners' ∪ GMap.listToSet csm.LearnersNext') : Int) ≤ 2 ^ 62 →
  ConfStateOk csm →
  -- (step 5) in place of `TraceLoggerOk cv.TraceLogger'`: a traced node is fresh
  (γ.reTrace ≠ none → BootFresh σ hs csm) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗ R ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"FirstIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + 1)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"LastIndex" si.v)) (Val #()))
         {{ RET (PairV #(W64 (uint.nat σ.prev.index' + σ.ents.length)) #interface.nil); R }}) ∗
      (□ {{ R }} (App (Val #(methods si.ty go!"InitialState" si.v)) (Val #()))
         {{ (hp cs : Loc) (al : Bool), RET (PairV (PairV #hp #cs) #interface.nil);
            hsOpt hp hs ∗ csPts cs DFrac.discard csm al ∗
            |={⊤}=> isStorageD sn (interface.ok si) ∗ ownStorage sn.unrec (interface.ok si) σ ∗
              trNoCut γ.reTrace (interface.ok si) ∗ R' }}) ∗
      trCapStart γ.reTrace γ cv.ID' cv.TraceLogger' (bootCfg vs) (bootPhase vs cv.ID') bootNone }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      R' ∗ trNoCut γ.reTrace (interface.ok si) ∗
      ∃ (s : NState) (r : Loc),
        rawNodeAt rn r cv.ID' si cs' cv.StepDownOnRemoval' cv.PreVote' hs σ cv.Applied' s ∗
        ⌜err = interface.nil⌝ ∗
        ⌜s.logst.sn = sn ∧ s.gh.sn = sn ∧ s.gh.tr = γ.reTrace ∧ s.cq = cv.CheckQuorum'⌝ ∗
        trCapB γ.reTrace γ r cv.ID' (bootCfg vs) false (bootPhase vs cv.ID') (bootAt vs cv.ID' 2) }}

end spec

end EtcdGrove
end Perennial
