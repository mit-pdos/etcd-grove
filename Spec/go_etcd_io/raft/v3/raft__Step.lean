/- Port of election_proof/spec_raft__Step.v (857d09190).

Lean notes:
* The spec mentions ghost state (`ownRaftGhost`, `isMessage`, `propAu`, `isProp`,
  `propTok`), so the section has the extra variable `[AllG GF]` (porting guide,
  "Section variables"), and fixes `hlc := HasLC.hasLC` (`[hG : HeapGS HasLC.hasLC GF]`
  instead of `{hlc : HasLC} [hG : HeapGS hlc GF]`): `ownRaftGhost` (through
  `raftCommitInv`) needs `[InvGS GF]`, which is `InvGS_gen .hasLC GF`, and the heap's
  invariant instance is one only at `hlc = .hasLC` -- the convention of Perennial's
  ports that state specs with invariants (`v3_proof/protocol.lean`, `context.lean`).
  Rocq's `heapGS` always carries that instance, so this is the faithful reading; a
  separate `[InvGS GF]` variable would be an invariant world unrelated to the WP's.
  Specs stated generically in `hlc` (every callee's) instantiate at `.hasLC`.
* Rocq's `Require Export New.proof.bytes` (for `wp_Equal`, used by the `MsgVote`
  branch's `Context` comparison) is `import Perennial.Proof.bytes`. The Rocq file
  imports `spec_raft__restore` before `step_lemmas` so that the model's `step` wins over
  any other `step` in scope; in Lean the model relation is `Step` and there is no
  clash.
* Rocq's `step_msg_types`/`step_msg` are `stepMsgTypes`/`StepMsg`; stdpp's
  `list.last` is `List.getLast?`.
* The context's existential is typed `ctx : List w8` (Rocq infers it from `↦*□` and
  the comparison with the `go_string` `campaignTransfer`).
* `[∗ list] e;Q ∈ ents;Qs, …` is `bigSepL2`; Rocq's `word.add (word.add (plast_index
  ps) (W64 1)) (W64 k)` (`k : nat`) is `plastIndex ps + W64 1 + W64 (k : Int)`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
-- `StableOk`, for `MsgStorageAppendResp` (2026-10-05)
public import Proof.go_etcd_io.raft.v3.InvReadylog
-- `SnapScope`, for `MsgSnap`
public import Spec.go_etcd_io.raft.v3.raft__restore
public import Proof.go_etcd_io.raft.v3.StepLemmas
-- `MsgBeat`
public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
-- `bytes.wp_Equal`, for the `MsgVote` branch's `Context` comparison.
public import Perennial.Proof.bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message types `Step` is specified for: every type its branches cover
(2026-10-02; until then only `MsgHup`/`MsgVote`/`MsgVoteResp`, `ElectionMsg`;
`MsgPreVote`/`MsgPreVoteResp` since 2026-10-04; the two local storage acknowledgements
`RawNode.Advance` steps, `MsgStorageAppendResp`/`MsgStorageApplyResp`, since
2026-10-05). -/
def stepMsgTypes : List w32 :=
  [MsgHup, MsgVote, MsgVoteResp, MsgApp, MsgAppResp, MsgHeartbeat,
   MsgHeartbeatResp, MsgBeat, MsgProp, MsgSnap, MsgPreVote, MsgPreVoteResp,
   MsgStorageAppendResp, MsgStorageApplyResp]

def StepMsg [FfiSyntax] (m : raftpb.Message) : Prop :=
  m.Type' ∈ stepMsgTypes

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, so that the heap's invariants are an `InvGS GF` (see the
-- Lean notes)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- The top-level dispatch, and **one spec like every other function**. The
per-message-type branches are proof structure, not specification: since 2026-09-17
they live in `proof_raft__Step_MsgHup.v`, `_MsgVote.v`, `_MsgVoteResp.v` and
(2026-10-02) `_MsgProp.v` (and below those, `_MsgVote_gt.v`, `_MsgVote_le.v`,
`_MsgVote_lt.v`, `_MsgVote_eq_novote.v`, `_MsgVote_eq_voted.v`), each a functor over
`STEP_POSTULATES` with no `Module Type` and no `Parameter`, so that `make -j` checks
them in parallel. Only `proof_raft__Step.v` and the combining files may `Require` one.
(An earlier version of this note said `Step` "is the one function with more than one
spec"; that was written before the first cut's three per-message-type `Module Type`s
were removed on 2026-09-14, and it is no longer true of anything here.)

This is **the only spec in this development that mentions ghost state**. Every
function below it is specified against `ownRaftPhys` alone, saying which state the
struct ends up refining and how the outbox grew; `Step` assembles those pure facts into
one `Step` witness and takes one `ownRaftGhost_step`. A caller that needs to know a
pending outgoing message is protocol-legal gets that from `ownRaftGhost_outbox`, not
from `ownRaftPhys`. -/
abbrev raft.Step.spec : Prop :=
  ∀ (cfg : GSet w64)
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (ps : PState)
    (m : raftpb.Message)
    -- The message's `Entries` (`[]` for a message without entries), bound here rather
    -- than in `"Hm"` since 2026-10-06 so that the postcondition can hand a proposal's
    -- updates back unchanged; and, for a `MsgProp`, the client's result predicate for
    -- each proposed entry (`"Hprops"`; unused for every other type).
    (ents : List raftpb.Entry) (Qs : List (w64 → w64 → IProp GF)),
  -- The ghost state is about one configuration, and it is this one. Without this the
  -- caller could hand `ownRaftGhost_step` a `cfg` of its own choosing -- a singleton
  -- one, say, in which the node is its own quorum -- and election safety would not
  -- hold. See `RaftNames`.
  γ.reCfg = cfg →
  StepMsg m →
  -- The node is a voter. `stepCandidate` needs this outright (its `poll` and
  -- `becomeLeader` both do) and `spec_stepCandidate_MsgVoteResp.v` says to thread it
  -- in "from the caller" -- but `Step` *is* the outermost caller, so it has to enter
  -- the development here. Under the no-learner, no-reconfiguration scope this is a
  -- property of the node, not of a particular call. Added 2026-09-16 for the
  -- `MsgVoteResp` branch.
  id ∈ cfg →
  -- A `MsgHup` is local (`Term = 0`) and may start an election, which increments the
  -- term; `send` panics if that wraps to zero.
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64) →
  (m.Type' = MsgVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0) →
  (m.Type' = MsgVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0) →
  -- Pre-vote (2026-10-04), by what the transport and the peers guarantee, like
  -- `MsgVote`; Go checks none of it. Two more:
  -- - a `MsgPreVote` of a higher term is answered at the node's own term when the
  --   candidate's log is behind (`Term: r.Term, Reject: true`; the term is not raised
  --   for a pre-vote), and `send` panics on a vote message with `Term = 0`. So a node
  --   at term `0` must find every pre-vote candidate up to date -- true of a node
  --   whose log holds nothing past term `0`, i.e. of every node etcd builds (a fresh
  --   node has an empty log; `Bootstrap` and `RestartNode` start at a term of at
  --   least the log's), but not implied by `ownRaftPhys`, which admits a persisted
  --   log ahead of the persisted term;
  -- - a `MsgPreVoteResp` at a pre-candidate may win, which runs the real `campaign`
  --   and increments the term: it must not wrap (as for `MsgHup`).
  (m.Type' = MsgPreVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
     (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true)) →
  (m.Type' = MsgPreVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64) →
  -- The replication types, by what the transport and the peers guarantee (Go checks
  -- none of it). A leader's `MsgApp`/`MsgHeartbeat`, and a `MsgHeartbeatResp`, come
  -- from another node: `send` never queues them to oneself. An accepting
  -- `MsgAppResp` may be the node's own (`appendEntry`'s self-acknowledgement); a
  -- rejecting one is not.
  (m.Type' = MsgApp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgAppResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (m.Reject' = true → m.From' ≠ id)) →
  (m.Type' = MsgHeartbeatResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- A leader's `MsgSnap`, likewise (2026-10-02).
  (m.Type' = MsgSnap →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- `MsgBeat` and `MsgProp` are local (`Term = 0`); a proposal is not yet stamped
  -- with a sender (`From = 0`), or is stamped with the node's own id
  -- (`RawNode.Propose` sets `From: r.id`; since 2026-10-06). The proposal's batch is
  -- constrained in `Hm` below, where its list is named.
  (m.Type' = MsgBeat → m.Term' = W64 0) →
  (m.Type' = MsgProp →
     m.Term' = W64 0 ∧
     (m.From' = W64 0 ∨ m.From' = id)) →
  -- The two local acknowledgements `RawNode.Advance` steps (2026-10-05), as
  -- `acceptReady` builds them (`InvRawnode.lean`, `appendAckMsg`, `applyAckMsg`). A
  -- `MsgStorageAppendResp` carries no snapshot (a pending snapshot is out of `Ready`'s
  -- scope; `appliedSnap` is phase 2), is not from a later term (it would make the node
  -- step down to a term no message brought), and -- when its `stableTo` runs (`Term`
  -- `0` or current, a nonzero `Index`) -- acknowledges only persisted entries
  -- (`StableOk`: Go compares only the term at `Index`). A `MsgStorageApplyResp` is
  -- local (`Term = 0`); its entries' last index is committed (the bound is in `"Hm"`,
  -- where the list is named).
  (m.Type' = MsgStorageAppendResp →
     m.Snapshot' = null ∧
     uint.Z m.Term' ≤ uint.Z s.term ∧
     (m.Term' = W64 0 ∨ m.Term' = s.term →
      m.Index' ≠ W64 0 →
      StableOk s.logst (entryID.mk m.LogTerm' m.Index'))) →
  (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  -- The one place the two layers meet. `s` is the physical abstract state
  -- `ownRaftPhys` is indexed by, `ps` the protocol state the ghost state is about,
  -- and `NStateRel` (`Defs.lean`) connects them: `ps` is `s`'s protocol fields,
  -- `r.step` agrees with the role, nothing is on loan.
  NStateRel s ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hghost" ∷ ownRaftGhost γ id ps ∗
      -- The message's `Entries` slice, holding `ents` (`[]` for a message without
      -- entries, `Entries = nil`):
      -- - a proposal is a local message whose batch the caller owns outright --
      --   `appendEntry` writes `Term`/`Index` into the entries -- while every network
      --   message's entries are read-only;
      -- - the slice's capacity, owned: `raftLog.maybeAppend` can adopt the caller's
      --   slice (`unstable.truncateAndAppend`'s replace arm), so a received `MsgApp`
      --   needs it;
      -- - a proposal's batch is non-empty (`stepLeader`'s `Panicf`), `EntryNormal`
      --   only (no conf change in scope) and short enough for `appendEntry`'s indices
      --   not to wrap;
      -- - what the message carries as a protocol message: its abstraction (`absMsg`,
      --   which needs the entries) was legitimately sent -- for every type but
      --   `MsgSnap`, whose abstraction is `absSnap` (`"Hsnap"` below).
      "Hm" ∷ (
         "Hents" ∷ (if m.Type' = MsgProp then m.Entries' ↦* ents
                    else m.Entries' ↦*□ ents) ∗
         "Hents_cap" ∷ ownSliceCap raftpb.Entry m.Entries' (DFrac.own 1) ∗
         "%Hprop" ∷ ⌜m.Type' = MsgProp →
                      ents ≠ [] ∧
                      (∀ e ∈ ents, e.Type' = EntryNormal) ∧
                      (ents.length : Int) < 2^61⌝ ∗
         "%Happly" ∷ ⌜m.Type' = MsgStorageApplyResp →
                       ∀ e, ents.getLast? = some e →
                       uint.Z e.Index' ≤ uint.Z s.logst.committed⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                            ⌜ty ≠ .snap⌝ -∗
                            isMessage γ (absMsg ty m ents))) ∗
      -- A proposal's client updates (2026-10-06), one per entry (`propAu`,
      -- `Protocol/GhostState.lean`: run when the entry, stamped, is committed).
      -- `bigSepL2` makes `Qs.length = ents.length`. Absent for every other type.
      "Hprops" ∷ (if m.Type' = MsgProp
                  then [∗list] e;Q ∈ ents;Qs, propAu γ e Q
                  else iprop(True)) ∗
      -- the `Context`: not the leader-transfer marker (out of scope), and empty on a
      -- heartbeat response (no read-index requests in scope: `bcastHeartbeat` sends
      -- `nil` and `handleHeartbeat` echoes it)
      "#Hctx" ∷ (∃ (ctx : List w8), m.Context' ↦*□ ctx ∗
                        ⌜ctx ≠ campaignTransfer⌝ ∗
                        ⌜m.Type' = MsgHeartbeatResp → ctx = []⌝) ∗
      -- A `MsgSnap`'s snapshot (2026-10-02): what `m.Snapshot` points to, read-only,
      -- and the list behind its `ConfState.Voters`; under the fixed-voter-set scope
      -- `SnapScope` (`Spec/raft__restore.lean`): the voters are `cfg`'s, `cfg` is
      -- zero-free, the other three sets are empty and `AutoLeave` is off (what
      -- `confchange.Restore`'s and `assertConfStatesEquivalent`'s specs cover), and
      -- the index is below `2^61` (a pending snapshot becomes the `Storage`'s
      -- boundary, which `isStorage`'s `Hbounded` bounds the same way). And the
      -- abstraction `absSnap` (`Defs.lean`) -- the snapshot's metadata, not `m`'s own
      -- `Index`/`LogTerm` -- was legitimately sent. The two added on 2026-10-02 with
      -- the branch (`W64 0 ∉ cfg`, `AutoLeave`, the index bound) are transport/client
      -- assumptions like the rest.
      "#Hsnap" ∷ □ (⌜m.Type' = MsgSnap⌝ -∗
         ∃ (sv : raftpb.Snapshot) (voters : List w64),
           m.Snapshot' ↦□ sv ∗
           sv.Metadata'.ConfState'.Voters' ↦*□ voters ∗
           ⌜SnapScope cfg sv voters⌝ ∗
           isMessage γ (absSnap m sv voters)) }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
  {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
      "Hphys" ∷ ownRaftPhys cfg r id s' ∗
      "Hghost" ∷ ownRaftGhost γ id ps' ∗
      "%Hrel" ∷ ⌜NStateRel s' ps'⌝ ∗
      "%Hrefines" ∷ ⌜∃ recv, Step cfg id ps recv ps'⌝ ∗
      -- only a proposal can be dropped, with `ErrProposalDropped`
      "Herr" ∷ (⌜err = interface.nil⌝ ∨
                (⌜m.Type' = MsgProp⌝ ∗
                 globalAddr ErrProposalDropped ↦□ err)) ∗
      -- A proposal (2026-10-06): appended at the leader (`Step.propose`: stamped at
      -- `ps`'s term and the indices after `ps`'s last), each update is registered at
      -- its entry's `(term, index)` and the client gets `isProp` and the token to
      -- collect `Q t i` with (`prop_collect`) once the entry is committed; otherwise
      -- -- forwarded by a follower, dropped (no leader known, a candidate,
      -- `appendEntry` refused it) -- the updates come back unrun.
      "Hprops" ∷ (if m.Type' = MsgProp
                  then (⌜err = interface.nil ∧ ps.role = .leader⌝ ∗
                        [∗list] k ↦ Q ∈ Qs, ∃ γp,
                          isProp γ ps.term (plastIndex ps + W64 1 + W64 (k : Int)) γp Q ∗
                          propTok γp)
                       ∨ ([∗list] e;Q ∈ ents;Qs, propAu γ e Q)
                  else iprop(True)) }}

end spec

end EtcdGrove
end Perennial
