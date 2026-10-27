/- Lean-first (no Rocq counterpart).

## `RawNode.Step` (rawnode.go:118), a message from the network

`Step(m)` drops a local message that does not come from a local target
(`ErrStepLocalMsg`) and a response from a node the tracker does not know
(`ErrStepPeerNotFound`); otherwise it is `rn.raft.Step(m)`.

Specified for the messages of replication and leader election (`NetMsgOk`): `MsgApp`,
`MsgAppResp`, `MsgVote`, `MsgVoteResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, and
(2026-10-13) of read-index: `MsgReadIndex`, `MsgReadIndexResp`; and (2026-10-13, for
`node.go`, whose `run` steps them all) leader transfer, `MsgTimeoutNow` and an unstamped
`MsgTransferLeader` (`TransferLeadership`'s), and the local `MsgForgetLeader`,
`MsgUnreachable`, `MsgSnapStatus`; (2026-10-17) pre-vote; (2026-10-20, D22 S-c) a leader's
`MsgSnap`, in the static mode, outside the cluster's no-snapshot mode (D22 S-c to S-d3a: with no
`Ready` outstanding; since D22 S-d3b, 2026-10-21, also between a `Ready` and its `Advance`, a
snapshot `Ready`'s included), its snapshot as `raft.Step` takes it (`"#Hsnap"`: the index bound,
`absSnap`); afterwards a snapshot may be pending (`RNState.psnap`), which the next `Ready` hands
out (`notes/decisions.md`, "D22 S-c carried out", "D22 S-d3b carried out") -- not a
`MsgTransferLeader` a follower forwarded (stamped:
`raft.Step` takes it only of a receiver that is no follower with a leader at its term,
`RestMsgOk`, a fact of the receiver's state no message carries) -- with what the transport
and the peers guarantee of them, which `raft.Step` takes as premises
(`Spec/raft__Step.lean`): addressed to this node, a nonzero term and sender, and not from
the node itself for a leader's `MsgApp`/`MsgHeartbeat`/`MsgReadIndexResp`, a heartbeat
response or a rejecting `MsgAppResp`. The unstamped types (`UnstampedType`, `Term = 0`):
a `MsgReadIndex` is a follower's forwarded request (or a local one, `node.ReadIndex`'s),
from and to anyone (any number of voters since 2026-10-14: stage F verified the single-voter
shortcut, stage R dropped the premise); it carries one read credit
(`rdCred`, `Hcred`), which `Ready` handed out with it. A `MsgTransferLeader` carries no
entries and no context, as `TransferLeadership` builds it. A `MsgTimeoutNow` makes the node
campaign one term past its own or the message's: neither may be the last term
(`HtimeoutNow`). The message was legitimately sent (`isMessage` of its abstraction) and its
`Entries` are read-only but for the slice's capacity, owned: `raftLog.maybeAppend` may
adopt the slice. As a message the transport delivers, it is the receiver's own copy. Until
2026-10-13 its `Context` was not the leader-transfer marker (a transfer's vote request is
now an ordinary one, as for `raft.Step`) and empty on a heartbeat response (a read-index
position is now what `isMessage` says it is).

The client sees only the term, which moves up to at most the message's (`TermStep`), or
(2026-10-13) for a `MsgTimeoutNow` one past it or the node's.
Every type may come between `Ready` and `Advance`, as in the concurrent `node.go`. A
`MsgApp` may truncate the unstable entries a `Ready` handed out (`offsetInProgress`
moves back below the entry the queued `MsgStorageAppendResp` acknowledges), and a later
one may put that very entry back; the acknowledgement is then still right, because the
storage agrees with the log up to it by Log Matching (`StepsOk`, `stableOk_of_stored`,
`InvRawnode.lean`). Until 2026-10-10 the spec took a `MsgApp` only with no `Ready`
outstanding (`m.Type' = MsgApp → rs.steps = []`).

Lean notes: like `RawNode.Propose.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.

raft v3.7 (2026-10-16, stage R5; `notes/decisions.md`, "The node layer over pointer messages"):
`Step` takes a `*pb.Message` (`ml`), for good, as `raft.Step` does (stage R4, Q3): `msgIn ml □
st` (the struct at `1`, the entries read-only, and, for a `MsgApp`, the `Entries` slice's
capacity), the record `st : MsgSt` (its scalars `st.msg`, entries, snapshot, context); every
premise is over `st` (`NetMsgOk id st`: the transfer request's "no entries, no context" is
`st.ents = []`, `st.ctx = []`). Nothing of the message is given back.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

-- (2026-10-16, stage R5) `netStepTypes`, `UnstampedType`, `NetMsgOk`, `NetMsgOk.restMsgOk`,
-- `DynNoSnap` and their lemmas moved to `InvRawnode.lean` (`node.go`'s `netP` states them).

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev RawNode.Step.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (ml : Loc) (st : MsgSt),
  NetMsgOk id st →
  -- (2026-10-14, stage B7 part 2) **no snapshot in the dynamic mode** (`DynNoSnap`): a
  -- snapshot restore at a dynamic configuration is stage B8. (Until 2026-10-20, D22 S-c,
  -- implied by `NetMsgOk`, which took no `MsgSnap` in either mode.)
  DynNoSnap rs st.msg →
  -- (2026-10-17) the term ceiling covers the message's term (a granted pre-vote answers at it)
  -- and, for a `MsgTimeoutNow` (until then: does not wrap the term), its campaign's term;
  -- the client raises the ceiling first (`ownRawNode_raise_tc`)
  uint.Z st.msg.Term' ≤ uint.Z rs.tc →
  (st.msg.Type' = MsgTimeoutNow → max (uint.Z rs.term) (uint.Z st.msg.Term') + 1 ≤ uint.Z rs.tc) →
  -- (2026-10-17) a pre-vote request only in a cluster started from a bootstrap log (`StartNode`):
  -- its nodes are past term `0`, at which a rejection could not be sent (`send` refuses a vote
  -- response of term `0`)
  (st.msg.Type' = MsgPreVote → γ.reBoot ≠ []) →
  -- (D19i part 1) the floor not raised past `applied` (a `MsgTimeoutNow` campaigns: `Campaign`'s)
  rs.flw = false →
  -- (2026-10-19, D21 M2r) a leader-transfer request only outside the cluster's no-transfer mode,
  -- where leader transfer is off (`NGhost.xf`, `NsLink`; D22 S-a: `RaftNames.reNoXfer`, until
  -- then the no-snapshot mode's flag)
  (st.msg.Type' = MsgTransferLeader → γ.reNoXfer = false) →
  -- (2026-10-20, D22 S-c) a snapshot only outside the cluster's no-snapshot mode, where no node
  -- sends one (`NsLink`, `raft.Step`'s premise). (D22 S-c to S-d3a also with no `Ready`
  -- outstanding, `rs.steps = []`: a restore replaces the log's boundary, which a queued
  -- `MsgStorageAppendResp` acknowledges against; since D22 S-d3b, 2026-10-21, the node keeps what
  -- the acknowledgement's miss after a restore needs, `ackInv`.)
  (st.msg.Type' = MsgSnap → γ.reNoSnap = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      -- (2026-10-16, stage R5) the message, taken for good as `raft.Step` takes it (until then
      -- `#Hents`, `Hents_cap`, `#Hctx`: the entries read-only with the slice's capacity, the
      -- context read-only)
      "Hm" ∷ msgIn ml DFrac.discard st ∗
      -- (2026-10-20, D22 S-c) but a snapshot's, whose abstraction is `absSnap` (`"#Hsnap"`)
      "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
        isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
      -- (2026-10-20, D22 S-c) a `MsgSnap`'s snapshot, as `raft.Step`'s `"#Hsnap"` takes it at the
      -- static mode (the only one a snapshot comes in, `DynNoSnap`): the snapshot the message
      -- holds, its `ConfState`'s lists well formed (`SnapScope`), the ghost state's voters, not
      -- joint, within the tracked bound (`GMode.SnapOk`), and its abstraction legitimately sent.
      -- (Since D22 S-b′4, 2026-10-20, `SnapScope` and `GMode.SnapOk` come from the message's
      -- configuration certificate, `isMessageC`'s `raftSnapCert`, once its lists name the node:
      -- only the index bound is left.)
      "#Hsnap" ∷ □ (⌜st.msg.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           -- (D22 S-b′4, 2026-10-20) the index bound only (the rest from the certificate)
           ⌜st.snap = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
           -- (D22 S-b′3, 2026-10-20) certified (`isMessageC`, `raft.Step`'s)
           isMessageC γ (absSnap st.msg sv scfg) ∗
           -- (D22 S-r, 2026-10-21) and its data certificate (`raft.Step`'s)
           snapDataOk γ sv.Metadata'.Index' sv.Data' ∗
           -- (2026-10-26, D22 J2, R-loc) and its receiver-local fact (`snapLocal`: for a node with
           -- a snapshot directory, its index saved there), which the node keeps while the
           -- snapshot is pending and a `Ready` that hands it out gives back
           snapLocal γ id sv.Metadata'.Index') ∗
      -- (2026-10-13) a read-index request's read credit
      "Hcred" ∷ rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (t : w64), RET #err;
      -- (2026-10-20, D22 S-c) after a snapshot, one may be pending (`RNState.psnap`)
      "Hrn" ∷ ownRawNode γ rn id
        { rs with term := t, psnap := rs.psnap || decide (st.msg.Type' = MsgSnap) } ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
               -- (2026-10-17) but a won pre-vote (on a response of the node's own term), at most
               -- to the message's term (one past it after a transfer's campaign)
               (st.msg.Type' ≠ MsgPreVoteResp →
                 uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term') +
                   (if st.msg.Type' = MsgTimeoutNow then 1 else 0))⌝ }}

end spec

end EtcdGrove
end Perennial
