# Status

**Last updated:** 2026-10-04 (branch `worktree-raft-replication`, pre-vote merged on top of `1fddf5333`; `origin/main` `4f48cb6de` merged in; not yet on `main`; the combined tree's build is being verified)

This file is a snapshot of where the proof *is*. It carries no history: how
something got this way is in [journal.md](journal.md), why a design was
chosen is in [decisions.md](decisions.md), and statements that turned out to
be false of the code are in [false-statements.md](false-statements.md).

## Goal

Verify etcd using Perennial/Grove, starting with its Raft implementation.

## Where things stand

This repo (`upamanyus/etcd-grove`) is a fork of `mit-pdos/perennial`. The
Perennial framework and the Goose toolchain are inherited wholesale and are
not the object of study — the etcd proofs are.

The Go code under verification is **not in this repo**. It lives in two
forks, both on branch `goose`, wired up in `new/etc/update-goose-new.py` and
`etc/ci-goose-check.py`:

- `upamanyus/etcd-raft` → translated into `new/code/go_etcd_io/raft/`
- `upamanyus/etcd` → translated into `new/code/go_etcd_io/etcd/`

### The raft proof

`new/proof/go_etcd_io/raft/` holds two developments side by side, both
reached from `new/should_build.v`: the election proof in `election_proof/`,
and the older read-index work in `v3_proof/`. They share only `base.v`.
(The election work moved out of `v3_proof/election/` on 2026-09-22; see
[decisions.md](decisions.md).)

- `v3_proof/base.v` — `IsPkgInit` instances for the raft package and its
  dependencies. Boilerplate; grows as new packages are pulled in.
- `election_proof/protocol.v` — the **protocol model**: the protocol node
  state `pstate.t` (term, vote, lead, role, votes, outbox, **and since
  2026-10-01 the log** -- `base`, `log`, `commit` -- and the leader's
  per-voter `matched`), the transition relation `step` (election rules plus
  the replication rules `step_app_accept/_stale/_reject`, `step_heartbeat`,
  `step_beat`, `step_app_resp`, `step_commit`, `step_send_apps`,
  `step_propose`, `step_prop_forward`), the ghost state (`own_raft_ghost`,
  `is_message`, `is_vote`, `is_leader`, and the per-term log authorities
  `is_term_log`/`is_entry`/`is_acked`/`is_committed`) and the safety
  statements. Constructed, not axiomatized, no Iris invariant.
  **Since 2026-10-01 this file may contain `Admitted`** (user's decision,
  [decisions.md](decisions.md)): two admits today (2026-10-03:
  `leader_completeness`, `state_machine_safety`; `snap_ok_message` is
  `Qed` since 2026-10-03), listed under "Trust base". Everything else in the development stays `Qed`.
- `election_proof/plog.v` — pure functions on an `(entryID, list Entry)`
  log (`plog_term_at`, `plog_matches`, `plog_find_conflict`,
  `plog_truncate_append`, `plog_maybe_append`, `plog_up_to_date`, ...),
  shared by the model and the `raftLog` specs. Design:
  [raft-replication-model.md](raft-replication-model.md).
- `election_proof/` (flat) and `election_proof/election.v` —
  the **implementation side**. One Go function per collection of four files:
  `spec_<fn>.v` (a `Module Type` with exactly one `Parameter`, the single
  place its Hoare triple is written), `postulates_<fn>.v`, `proof_<fn>.v` (a
  functor ascribed to the signature) and `link_<fn>.v`. **125 collections**
  (98 on 2026-09-29; the 27 added on 2026-10-01/02 are the replication
  path: `raftLog.{matchTerm,findConflict,findConflictByTerm,commitTo,
  maybeCommit,maybeAppend,zeroTermOnOutOfBounds}`, `raft.{handleAppendEntries,
  handleHeartbeat,sendHeartbeat,bcastHeartbeat,bcastHeartbeatWithCtx,
  maybeCommit}`, `Progress.{MaybeUpdate,MaybeDecrTo,BecomeProbe,CanBumpCommit}`,
  `Inflights.FreeLE`, `ProgressTracker.Committed`, `MajorityConfig/
  JointConfig.CommittedIndex`, `matchAckIndexer.AckedIndex`,
  `readOnly.heartbeatCtx`, `releasePendingReadIndexMessages`, `traceCommit`,
  `pbEntryID`, `logSliceFromMsgApp`). The three `stepX` collections are now
  `stepFollower`, `stepCandidate`, `stepLeader` (renamed from
  `*_MsgVoteResp`), each **one spec over every message type `Step`
  dispatches to it** (the last arms are in flight, see "In flight").
  Shared predicates live in `defs.v`, `inv_*.v` and `step_lemmas.v`, outside
  the module system. A function whose proof needs several files gets a
  `proof_<fn>_helpers/` directory (two today: `raft__Step`, with eight,
  and `MajorityConfig__VoteResult`).
  `election.v` is an aggregator plus `raft_election_safety`.
- `v3_proof/readonly.v` — the read-index/heartbeat protocol development.
  **Not on the election path**; nothing under `election_proof/` requires it.
  Until 2026-09-22 *nothing at all* required it, so `make ci` had never
  compiled it; `should_build.v:51` now requires it as a stopgap pending a
  clean-up of the old proofs. It checks (`-vok` clean).
- `v3_proof/protocol.v` — an axiomatized node-level interface (`is_node`,
  `node.Ready`, `node.Advance`, `node.Propose`). **Not on the election path.**

`etc/check-module-discipline.py` enforces the layout. It reads the program
expression out of each triple rather than trusting names, so it reports which
Go function a spec really specifies, and errors on a triple outside the
spec/proof shape, two triples for one function, a malformed spec file, an
incomplete collection, or a name absent from `new/code/`.

    etc/check-module-discipline.py --scope election_proof   # 3 findings, all warnings (2026-10-02)
    etc/check-module-discipline.py --summary
    etc/check-module-discipline.py --selftest

Its companion `etc/tcb-report.py` views the same tree for trust rather than
structure. Both share `etc/rocqscan.py`.

### Rest of etcd

`new/proof/go_etcd_io/etcd/` carries earlier work on the client (`client/v3`,
including a leasing protocol proof), `pkg/v3`, `api/v3` protobuf packages and
`server/v3/etcdserver`. Context for the raft work, not the current focus.

## The three layers, and the one-predicate rule

The proof is a refinement in three layers, each with its own state type
(notes/decisions.md, "Three layers", 2026-09-22):

1. **Go code and heap → `nstate.t`** (`election_proof/defs.v`), by
   `own_raft_phys r id s` (`election_proof/inv_raft_phys.v`). Every Go-level spec
   is a pre/postcondition on it. `nstate.t` carries the six protocol fields
   plus `stepfn` (`r.step`), `progress` (the progress map), `log`
   (`r.raftLog`), `logst` (the log's state) and `prvals` (each peer's
   `Progress`/`Inflights` values). **Every field is physical state**;
   nothing is ever lent out of `own_raft_phys` (since 2026-09-29).
2. **`nstate.t` → `pstate.t`** (`election_proof/protocol.v`), by `nstate_rel`
   (`defs.v`). Only `Step`'s spec mentions both.
3. **`pstate.t` → protocol properties**: `own_raft_ghost`, `step`,
   `raft_election_safety`.

**The rule: one ownership predicate per object.** If a function cannot be
specified with `own_raft_phys`, refine `nstate.t` and `own_raft_phys` until
it can. Never add a variant predicate, a parameterised copy, or a spec on
raw pieces of the struct. Three such variants (`own_raft_phys_at`,
`own_raft_bare`, `own_raft_notrk`) existed until 2026-09-22 and were removed;
see gotchas.md for the checklist. `hup`, the `Step` helpers and `Step`
take `nstate_wf s` (`r.step` matches the role).

The same rule holds for every object the struct points at, and since
2026-09-23 it is met on the election path: `own_tracker cfg tv votes prs pvs`
(indexed by the progress map and the `Progress` values), `own_progress pr pv iv`,
`own_inflights l iv buf`, `own_raftLog l ls` with `ls : logstate.t`
(entry list, `committed`, `applied`),
`own_unstable u uv uents`, and `own_read_only ro`. Since 2026-09-29
the log's state **is** in `nstate.t` (`logst : logstate.t`): `own_raft_phys`
always owns `own_raftLog rv.raftLog s.logst`, the log holds its entries
read-only (`↦*□`), so what `raftLog.slice`/`entries` return is the
caller's for good with nothing lent, and each peer's `Progress` value is
in `nstate.prvals`, so a function that reads a `Progress`, calls into the
struct and then writes it borrows it around each access instead of
holding the tracker on loan (decisions.md, 2026-09-29, twice).

## What is proved

Every Hoare triple on the election path is `Qed` — **274 lemmas**, 98
discharged signatures — except one admission signed off on for now
(below). **The results are the first two of these three**; the third is an
internal lemma that nothing uses yet — a *root lemma*, in `tcb-report`'s
terms (decisions.md, 2026-09-21: what this development is for is verified
specs of Go functions):

- **`Step.wp_raft__Step`** (`election_proof/spec_raft__Step.v`): running `Step` on
  any message of the ten types in scope -- `MsgHup`, `MsgVote`, `MsgVoteResp`,
  `MsgApp`, `MsgAppResp`, `MsgHeartbeat`, `MsgHeartbeatResp`, `MsgBeat`,
  `MsgProp`, since 2026-10-02 (late) `MsgSnap`, and since 2026-10-04
  `MsgPreVote`/`MsgPreVoteResp` (`step_msg`, twelve types) -- takes `own_raft_phys` from a physical state `s`
  with `nstate_rel s ps` to some `s'` with `nstate_rel s' ps'`, and moves
  `own_raft_ghost` from `ps` to `ps'` at the same time, with
  `∃ recv, step cfg id ps recv ps'`; `err` is `nil`, or `ErrProposalDropped`
  for a dropped `MsgProp`. **`Qed` for all ten since 2026-10-02.** The
  precondition takes the message's `Entries` (owned outright for a local
  `MsgProp`, which `appendEntry` stamps; read-only with their capacity for a
  network message, which `truncateAndAppend` may adopt), the `is_message`
  fact at `abs_msg ty m ents`, and per-type transport premises (`To = id`,
  `Term ≠ 0`, `From ≠ 0`, `From ≠ id` for leader messages and responses the
  node would answer; `Term = 0`/`From = 0` for the local ones). One branch
  per type under `proof_raft__Step_helpers/` (split by term case), and
  `proof_raft__Step.v`'s dispatch derives each branch's protocol premises
  from the ghost state (`app_recv_wf`, `app_no_conflict_below_commit`,
  `heartbeat_commit_le_last`, `own_raft_ghost_lead_ok`,
  `own_raft_ghost_follower_votes`, `is_leader_unique`).
- **Everything `Step` dispatches to is specified and `Qed`** (2026-10-01/02):
  `stepFollower`, `stepCandidate`, `stepLeader`, each one spec total over the
  seven types `r.step` sees, and the whole call tree below them, stated on
  `own_raft_phys`/`own_raftLog`/`own_Progress` with `plog.v`'s functions:
  the follower's append decision (`raftLog.maybeAppend` through
  `matchTerm`/`findConflict`/`truncateAndAppend`'s three arms/`commitTo`),
  the leader's commit (`maybeCommit` through `ProgressTracker.Committed`,
  returning `is_quorum cfg (acked_by …)`), the heartbeat chain,
  `appendEntry` for an arbitrary `EntryNormal` batch with its drop path,
  and proposal forwarding.
- **`NewRaft.wp_newRaft`** (`election_proof/spec_newRaft.v`, 2026-09-24):
  the **constructor**. From a `Config` and a `Storage` it returns
  `own_raft_phys (list_to_set voters) r cv.ID s` at a state that is
  `nstate_wf`, a follower with no leader, an empty tally and outbox, and
  `term`/`vote` the persisted `HardState`'s; `newRaft_post_init`
  (`election.v`) turns that into `nstate_rel s init_pstate` for an empty
  `HardState`, the state `own_raft_ghost_alloc` starts every node in. So
  `own_raft_phys` is established by code raft actually runs — *given* a
  `Storage` meeting `is_Storage`; see "What still needs fixing", item 1.
- **`raft_election_safety`** (`election.v`): two nodes whose ghost state says
  "leader in term `t`" are the same node.

**`raft_election_safety` is code-free.** It relates two `own_raft_ghost`
assertions; `wp_raft__Step` is the only bridge to the Go code, and it is a
*single-call* triple. Nothing yet composes it into a running node or a
cluster. Read the next two sections before quoting the result.

**No spec below `Step` touches ghost state.** A callee's spec says only which
state the struct ends up refining and how the outbox grew — never that the
transition is legal. `own_raft_ghost` therefore appears in exactly one spec
and `own_raft_ghost_step` is applied in exactly one proof file. If you find
yourself adding `own_raft_ghost` to a callee, that is the thing this layout
exists to prevent.

**Program proofs do not unfold `own_raft_phys`** -- it is sealed. Every
access to the raft struct is a lemma from the interface section at the end
of `inv_raft_phys.v`, named explicitly: one triple per field load and store,
accessors for the tracker, one peer's `Progress`, the log, message queues
and `readOnly` (decisions.md, 2026-09-24). `proof_raft__poll.v` is the
short worked example (the tracker accessor); `proof_raft__reset.v` the
long one (a `Visit` closure whose invariant is the tracker accessor's
wand); `proof_raft__maybeSendAppend.v` borrows one `Progress` around a
`send`. The traps are in
[gotchas.md](gotchas.md), "Working against the sealed `own_raft_phys`".

## The verified configuration

Everything above holds **only** under these assumptions. They are premises of
`wp_raft__Step_body` and of `own_raft_phys`, not claims about etcd.

| assumption | where |
|---|---|
| Only the twelve `step_msg` types (since 2026-10-04 with `MsgPreVote`/`MsgPreVoteResp`) are passed to `Step`; the read-index, leader-transfer, check-quorum and storage-response types are taken to be dropped by the network (phase 3). A received `MsgApp`/`MsgHeartbeat`/`MsgHeartbeatResp`, and a rejecting `MsgAppResp`, has `From ≠ id` (a node never sends itself one: `send` panics) | `step_msg`, `spec_raft__Step.v` |
| A received `MsgApp`'s entries are `EntryNormal`, contiguous from `Index+1`, and conflict only above the receiver's commit index; a received `Heartbeat`'s `Commit` is at most the receiver's last index. All four are proved from `own_raft_ghost` and `is_message` (`app_recv_wf`, `app_no_conflict_below_commit`, `heartbeat_commit_le_last`; since 2026-10-02 none is admitted) | `protocol.v` |
| No read-index requests: `readOnly.unconfirmedReads` and `pendingReadIndexMessages` are empty, so `heartbeatCtx` is `nil` and a `MsgHeartbeatResp` carries an empty `Context` | `inv_misc.v` |
| `disableProposalForwarding = false` (`newRaft` copies the `Config` field; a scope premise of `newRaft`'s spec) | `inv_raft_phys.v`, `spec_newRaft.v` |
| No proposals, no read-only requests | scope |
| No reconfiguration, no learners; the voter set `cfg` is fixed, and **no `EntryConfChange` is anywhere in the log** | `HnoConfChange`, `inv_raftlog.v:139` |
| A received `MsgSnap` carries a snapshot (`m.Snapshot ↦□ sv`, its voters `↦*□`) whose `ConfState` is `cfg`'s voters only (no learners, not joint, `AutoLeave` off), with `0 ∉ cfg` and `Metadata.Index < 2^61`; it is `To = id`, `Term ≠ 0`, `From ≠ 0`, `From ≠ id` (`snap_scope`, `"Hsnap"`). A pending snapshot is never stored (`stableSnapTo`, `Ready` out of scope) | `spec_raft__Step.v`, `spec_raft__restore.v` |
| No check-quorum (`checkQuorum = false`). **Pre-vote is in scope since 2026-10-04**: `nstate.prevote` is `r.preVote`, either value, and `newRaft` copies `Config.PreVote` | `inv_raft_phys.v` (`HnoCheckQuorum`, `Hprevote`) |
| Pre-vote only: a node at term `0` finds every `MsgPreVote` candidate up to date (else it would reject at `Term: 0`, which `send` panics on; true of every node etcd builds, not implied by `own_raft_phys`); a `MsgPreVoteResp` cannot make the term wrap (`uint.Z s.term + 1 < 2^64`, a pre-candidate's win runs `campaign`). `MsgPreVote`/`MsgPreVoteResp` are `To = id`, `Term ≠ 0`, `From ≠ 0` (and `From ≠ id` for `MsgPreVote`) | `spec_raft__Step.v` |
| No leader transfer (`leadTransferee = 0`, `Context ≠ campaignTransfer`) | `spec_raft__Step.v` |
| Node ids are nonzero; `id ∈ cfg`; the ghost state's `cfg` is the physical one (`γ.(re_cfg) = cfg`) | `spec_raft__Step.v`, `own_raft_ghost` |
| A `MsgHup` cannot make the term wrap: `uint.Z s.term + 1 < 2^64` | `spec_raft__Step.v` |
| Incoming `MsgVote`/`MsgVoteResp` are addressed to this node and have `Term ≠ 0`, `From ≠ 0`. **Go checks none of these** — they are assumptions about the transport and about peers | `spec_raft__Step.v` |
| Crash safety is out of scope. `Step` is a `wp`, not a `wpc` | — |
| `newRaft` only: `Config.validate` passes, with a non-nil `Logger` (Go would install its default one) | `config_valid`, `spec_Config__validate.v` |
| `newRaft` only: **`MaxInflightMsgs < 2^62`** — not implied by `validate`, which checks only `> 0`; `own_tracker`'s `HmaxInfl` needs it | `spec_newRaft.v` |
| `newRaft` only: the persisted `ConfState` is **voters-only, non-empty, duplicate-free and zero-free**. An empty one is what a node joining an existing cluster starts with (`StartNode` with no peers), so such a node is outside the development until it gets a snapshot | `spec_newRaft.v`, `spec_confchange_Restore.v` |
| `newRaft` only: the stored entries have contiguous indices and no conf change; `hs.Commit` and `Config.Applied` lie where `loadState`/`appliedTo` would otherwise panic; `InitialState` returns `(hs, cs, nil)` | `spec_newRaft.v` |

Two of these are not restrictions a deployment can honour as written:
`HnoConfChange`, and — if you care about etcd's defaults — check-quorum,
which etcd's server turns on (pre-vote, the other default, is covered
since 2026-10-04).

## Done on 2026-10-01/02, and what is next

Branch `worktree-raft-replication`, pushed at every merge; `make ci` exit 0
at `3574293f1` (544 files). Landed: the model with the log and the leader's
`matched`; `plog.v`; 27 new collections and the widened `stepX` specs;
`Step` over nine message types; the public tracker predicates
(`own_Progress`/`own_Inflights` over `progress.t`/`inflights.t`,
`own_tracker` over `trk.t`, `nstate.prvals : gmap w64 progress.t`; user's
request, 2026-10-02). Design and history:
[raft-replication-model.md](raft-replication-model.md), the journal.

Next, in the user's order: **snapshots** (`MsgSnap`/`restore`; design in the
model note, "Phase 2"), then pre-vote, reconfiguration, read-only.
Also pending: `origin/main` has four commits (`4f48cb6de`) not merged into
the branch, one of which (`873b7d26a`) touches the election cone.

**Snapshots, model side, done** (2026-10-02, `e57c313f2`): `msg.voters`,
`abs_snap`, `is_message` for `Snap`, rules `step_snap_restore/_fastfwd/_stale`
(ghost updates Qed), `send_ok`'s `MsgSnap` clause, `Step`'s `"Hsnap"`
conjunct (unused until `step_msg` gets `MsgSnap`). One new admit,
`snap_ok_message` -- a client-`Storage` assumption (the snapshot's metadata
is a committed entry id), not a protocol fact; and a known weakness: a
*queued* `MsgSnap`'s abstraction (`msg_abs`) is not yet tied to the heap
behind `m.Snapshot`, because `send` has no snapshot precondition and
`raftLog.snapshot` returns the value -- tightening needs the
`Storage.Snapshot` contract to pin the metadata and voters. Next: the log
side (`logstate.snap`, `restore`, `handleSnapshot`, the `MsgSnap` `Step`
branch); see raft-replication-model.md, "Phase 2".

**Snapshots, receiver side, done** (2026-10-02, branch
`worktree-agent-a6ef9862e0d3133ee`, not yet merged): `logstate.snap` with
the log proofs' snapshot arms, `unstable/raftLog/raft.restore`,
`raft.handleSnapshot`, the `stepFollower`/`stepCandidate` `MsgSnap` arms,
`promotable`'s snapshot conjunct, and the `MsgSnap` `Step` branch refining
`step_snap_stale/_fastfwd/_restore`.  New `Step` premises for `MsgSnap`:
`0 ∉ cfg`, `AutoLeave = false`, `Index < 2^61` (inside `"Hsnap"`'s
`snap_scope`).  Details: raft-replication-model.md, "Phase 2 … Done
2026-10-02: the log and implementation side".

**Pre-vote, done** (2026-10-04, branch `worktree-agent-a55b1ab28ca9c10e1`
from `1e5c18fce`, not yet merged): `nstate.role : prole.t` (four physical
roles, `PreCandidate` read as a follower with no leader and an empty tally
by `to_pstate`), `nstate.prevote`, `becomePreCandidate`, `campaign`/`hup`
for `campaignPreElection`, `stepCandidate` in `StatePreCandidate`, `Step`
over `MsgPreVote`/`MsgPreVoteResp` and the live stale-term `MsgAppResp`.
Three protocol rules appended to `step` (`step_send_free`, `step_abandon`,
`step_zero_ack`; ghost cases `Qed`).  Details: raft-replication-model.md,
"Phase 3 … Pre-vote … Done 2026-10-04".  Next: reconfiguration.

**Snapshots, sender side, done** (2026-10-03, branch
`worktree-agent-a4805cdd87b17c9a2` from `1de11b38d`, not yet merged): a
queued `MsgSnap`'s `msg_abs` reads `m.Snapshot ↦□ sv` and the voters'
`↦*□` (`send` takes them, `"Hsnap"`; `maybeSendSnapshot` persists its
local `snapshot`); `own_Storage` names the storage's snapshot `ss`,
`HSnapshot` returns it with its voters read-only, and `own_raftLog` keeps
`stored_snap_ok` (`ss` committed and in the log) -- a new `newRaft`/
`newLogWithSize` premise `ss.index = 0 ∨ ss = prev`; `snap_ok` carries
`index ≤ commit` and the log fact; `own_log_ghost` gained `base_ok`;
**`snap_ok_message` is `Qed`**.  Details: raft-replication-model.md,
"Phase 2 … Done 2026-10-03: the sender side".  Next: pre-vote.

## What still needs fixing

Ranked by how much the proof's meaning depends on it. Unclaimed; pick one and
say so in the journal.

1. ~~**`own_raft_phys`'s constructor rests on `is_Storage`, and there is no
   `is_Storage` instance.**~~ **Instance proved 2026-10-04**:
   `is_Storage_MemoryStorage` (`election_proof/memstorage_instance.v`)
   shows raft's own `MemoryStorage` meets the contract, through seven
   collections (`MemoryStorage.{LastIndex,FirstIndex,Term,Entries,Snapshot}`
   and the two private index helpers) stated on `own_MemoryStorage`
   (`inv_memstorage.v`: the struct behind its `sync.Mutex`, the state split
   as a `ghost_var` between the lock invariant and the predicate). The
   contract is factored as `is_Storage_with P st` with `is_Storage st :=
   is_Storage_with (own_Storage st) st`; `own_Storage` is still the
   `Axiom`, so the 14 axioms are unchanged. Switching the development to
   MemoryStorage-only is one definition away (`own_Storage st … := ∃ ms,
   ⌜st = mk_ok (*MemoryStorage) ms⌝ ∗ own_MemoryStorage ms …`) and would
   remove that axiom; not done, to keep `newRaft` general. **One
   restriction found**: the contract requires `Snapshot` to return a
   non-empty snapshot or `ErrSnapshotTemporarilyUnavailable` (raft panics on
   an empty one in `maybeSendSnapshot`), while a fresh `MemoryStorage`
   returns the zero snapshot with a nil error -- so `own_MemoryStorage`
   requires `ss.index ≠ 0`, i.e. a storage that has a snapshot. The
   remaining parts of this item: `newRaft` is proved (2026-09-24), so
   `own_raft_phys` is no longer only satisfiable by inspection: the struct
   `newRaft` builds satisfies it. But `newRaft`'s spec takes `is_Storage`,
   `own_Storage` and an `InitialState` triple as premises, and `own_Storage`
   is an `Axiom` with no model -- so the chain ends at an unexhibited
   storage. Proving `MemoryStorage` against `is_Storage` closes it. The
   `newRaft` work also found, and left open:
   - **`own_raftLog` forgets which `Storage` it holds.** `logstate.t` has no
     storage field, so `own_Storage` sits inside the log at `lv.storage` for
     an `lv` no caller can name. `newRaft` calls `c.Storage.InitialState()`
     *after* building the log, through the `Config`'s alias of the same
     interface value, and needs the log's `own_Storage` for it; nothing
     relates the two. Worked around by stating `newLogWithSize`'s
     postcondition in `own_raftLog_unfold`'s unfolded form plus
     `lv.storage = st` -- a spec on raw pieces, against the one-predicate
     rule. The fix is a `storage` field in `logstate.t` (19 files, 53 sites,
     mechanical).
   - **Two `Axiom`s about core raft**: `confchange.Restore` and
     `raftpb.ConfState.Equivalent` are not translated
     (`confchange.v.toml` is `translate = ["Changer"]`, `raftpb` is
     types-only), so `spec_confchange_Restore.v` and
     `spec_ConfState__Equivalent.v` state them for the voters-only case,
     each checked against the Go in its comment. Translate `confchange` and
     prove `Restore` (`Simple`/`apply`/`checkInvariants`).
   - `own_tracker`'s `HmaxInfl` comment claimed `validate` bounds
     `MaxInflightMsgs`; it does not ([false-statements.md](false-statements.md)).
2. **`HnoConfChange` is false of a real cluster.** `inv_raftlog.v:139`
   requires `Forall (λ e, Type = EntryNormal) (sents ++ uents)` — the *whole*
   log — while `RawNode.Bootstrap` (`new/code/go_etcd_io/raft/v3.v:391`)
   writes `EntryConfChange` entries at `v3.v:447`, and `StartNode` calls it.
   So `own_raft_phys` is unsatisfiable for a freshly bootstrapped node until
   compaction. Only "no conf change in `(applied, committed]`" is needed;
   weakening it is cheap and should happen.
3. **`Ready` / `advance` / `acceptReady` are unverified.** No collection
   exists. They are the only thing that drains `msgs` and `msgsAfterAppend`,
   so `step_drain` — the model rule that exists for exactly this — refines
   nothing, and nothing shows `own_raft_phys` survives a drain. This blocks
   composing `Step` into a running node.
4. **`tick` needs a scope decision.** `tickElection` calls `Step(MsgHup)`
   (`v3.v:3497`), which is covered. `tickHeartbeat` calls `Step(MsgBeat)`
   unconditionally (`v3.v:3552`); its `Step(MsgCheckQuorum)` (`v3.v:3523`) is
   guarded by `r.checkQuorum` and so is dead under the scope. Either
   `tickHeartbeat` is out of scope — a leader never heartbeats, harmless for
   safety — or `MsgBeat` needs a branch. Decide and write it down; the scope
   table above does not currently say.
5. ~~**`isUpToDate` is unconstrained**~~ — **done 2026-10-01**:
   `raftLog.isUpToDate`, `lastEntryID`, `term` and `unstable.maybeTerm` pin
   their results (`plog_up_to_date`, `plog_last`, `plog_term_at`), and
   `step_grant_vote` carries the up-to-date premise. What remains is the
   protocol-level use of it: `leader_completeness` is admitted.
5a. ~~**`snap_ok_message` (admitted)**~~ -- **done 2026-10-03**: `Qed`,
   from `snap_ok`'s new commit bound and log fact, which
   `maybeSendSnapshot` gets from `raftLog.snapshot` (`HSnapshot` names
   the storage's snapshot `ss`; `own_raftLog`'s `stored_snap_ok` relates
   it to `committed`), plus `own_log_ghost`'s `base_ok`.  `msg_abs`'s
   `MsgSnap` case is tied to the heap.  Remaining scope cost: `newRaft`
   needs the storage's snapshot to be empty or at its first index.
5b. **`leader_completeness` and `state_machine_safety` (admitted,
   `protocol.v`)** -- the other three of the former five
   (`heartbeat_commit_le_last`, `app_no_conflict_below_commit`,
   `log_matching`) are `Qed` since 2026-10-02 (journal). These two are
   **not provable as stated**: they hold two nodes' ghost state, and the
   argument needs a third node (the voter in the commit quorum and the
   election quorum) to have behaved -- its votes and acknowledgements are
   fragments of its own maps, unconstrained without its `own_raft_ghost`.
   A proof needs (1) a cluster-wide statement (every voter's
   `own_raft_ghost`, or an Iris invariant over them), (2) a per-node
   history invariant tying each vote to the voter's log at the time and to
   its earlier acknowledgements, (3) `is_committed` naming the committed
   entries. Spelled out in `leader_completeness`'s comment. Nothing
   downstream consumes either lemma.
5c. **Two assumptions on the client `Storage` were added** (`inv_storage.v`):
   `Entries` returns a prefix of the stored entries from `lo` (its documented
   contract; `MemoryStorage` meets it). Listed so an auditor sees them.
6. **Bring `readonly.v` and `protocol.v` into the module discipline.** Eleven
   triples are still stated loose. One is a real duplicate:
   `raft.stepLeader` has a second triple in `readonly.v` against a second
   ownership story (`own_raft`), `Admitted` with postcondition `True` and no
   users. Resolving it means deciding whether `own_raft` or `own_raft_phys`
   survives.
8. ~~Decide the top-level Raft correctness statement~~ — **decided
   2026-09-21** ([decisions.md](decisions.md)): the result is verified specs
   for the top-level Go functions, and protocol facts such as election
   safety are internal lemmas in their service. What is left of this is
   items 4 and 9.
7. **Discharge `protocol.v`'s `Section axioms`** against the translated code,
   or record why each stays an axiom. Then extend past `Propose` to the rest
   of the `node` interface.
10. Two stale comments, both misleading to an auditor: `election.v:20-23` says
   the `inv_*.v` files hold the log and tracker as `Axiom`s (they are
   definitions), and `election_proof/protocol.v:55-58` motivates including
   `App`/`Heartbeat` in the model by the higher-term step-down — true of the
   code, but under the scope above that transition is never received, so the
   rule refines nothing and a reader could take it for a discharged
   obligation.

## Trust base

**An audit is two commands, and neither substitutes for the other**:
`make` first — the only thing that checks proofs — then `etc/tcb-report.py`,
whose whole job is what the build cannot check. What each establishes, the
known gaps and the plan are in [tcb-accounting.md](tcb-accounting.md).

`etc/tcb-report.py` on the election path (`--scope election_proof`,
2026-10-05, at `93d1d65da`): **14 `Axiom` and 3 `Admitted`** -- the one
signed off on in `raftLog.slice`, and the two safety theorems
`leader_completeness` and `state_machine_safety`, which **cannot be proved
as stated**: they quantify over two nodes' ghost states, and the argument
needs the third node that is in both the commit quorum and the election
quorum (its votes and acks live in its own ghost maps) -- they are being
restated over the whole cluster, see item 5b. `heartbeat_commit_le_last`,
`app_no_conflict_below_commit`, `log_matching` (2026-10-02) and
`snap_ok_message` (2026-10-03) are proved. 626 `Qed` lemmas, 141
collections (pre-vote, the read-only record and the `MemoryStorage`
instance included), two results (`Step`, `newRaft`), 169 definitions,
1,545 lines; `make ci` exit 0 (619 files). The whole-raft numbers (`v3_proof/`
included) are the old ones plus these.

    R=new/proof/go_etcd_io/raft      # required; the tool names no development
    etc/tcb-report.py --proof-root $R                  # summary, and which files are incomplete
    etc/tcb-report.py --proof-root $R --scope election_proof   # the cone the build reaches
    etc/tcb-report.py --proof-root $R --view assumed   # every axiom and admit, classified
    etc/tcb-report.py --proof-root $R --view surface   # results, root lemmas, what they rest on

It reports **results** (Go-function Hoare triples nothing else calls)
separately from **root lemmas** (stated facts nothing uses yet, such as
`raft_election_safety` — not results, not counted), splits the assumed
into *Hoare triples about Go code / undefined declarations / other*, and
lists any file under the proof root that the build does not reach.

**Do not count these by hand, and do not grep for them.** A grep over-counts:
doc comments quote probe lemmas ending in `Admitted.`, and `spec_*.v` files
are full of `Parameter`s.

The count of axioms is the smaller half. The **definitions** the results
reach — 74 on the election path, 802 lines — are the rest of it:
`wp_raft__Step` says nothing if `nstate.t`, `nstate_rel`, `pstate.t`,
`step` or `own_raft_phys` is wrong, and none of those is an axiom.

### What the keywords mean

The *keyword* says which kind of debt and the *file name* says which
function. File kind carries no distinction.

- an **`Axiom`** means **outside the raft protocol**, and there should be very
  few. A trust-boundary triple is declared with `Axiom` inside its functor,
  which still discharges the signature's `Parameter` and still shows up in
  `Print Assumptions`;
- an **`Admitted` `Lemma`** means **in scope but unfinished**, wherever it is;
- a **`Parameter` in a `spec_*.v`** is neither — it is discharged by the
  functor ascribed to that signature, so it never reaches
  `Print Assumptions`.

The only thing the election development may assume outright is the top-level
scope. Everything in **core raft** — the log, the tracker, `Progress`,
`bcastAppend` — must be constructed and proved.

### The fourteen axioms on the election path

Twelve are outside the raft protocol. **Two are about core raft** --
`wp_confchange_Restore` and `wp_ConfState__Equivalent`, stated because the
code is not translated -- and are debt (item 1 above). None feeds a vote or
a leader decision: all four added on 2026-09-24 are reached only from
`newRaft`, so none can hide an election-safety bug in `Step`.

| axiom | file | why it is outside raft |
|---|---|---|
| `is_Logger`, `is_Logger_pers`, `wp_Logger__logf` | `inv_logger.v` | client-supplied interface. Covers only the **non-panicking** methods — a path reaching `Panic`/`Panicf` must be shown unreachable |
| `own_Storage` | `inv_storage.v` | `raftLog.storage` is client-supplied; raft ships only `MemoryStorage`, for tests. A predicate, not a triple. Its contract `is_Storage` is real and constrains `Entries`, `Term`, `Snapshot` and a `< 2^61` bound on the stable last index. Since 2026-09-29 `Entries` hands its result out **read-only for good** (`s ↦*□ es`, no wand back) — the `Storage` interface's documented contract (`storage.go:56-67`: entries "must not be mutated, neither by the Storage implementation nor the caller"), which `MemoryStorage` meets |
| `own_big_Int`, `wp_big_NewInt`, `wp_big_Int__Int64`, `wp_rand_Int` | `inv_big.v`, `proof_big_*.v`, `proof_rand_Int.v` | `math/big` and the RNG behind `resetRandomizedElectionTimeout` |
| `wp_slices_Sort` | `proof_slices_Sort.v` | not translated. Permutation-only postcondition |
| `wp_Entry__Size` | `proof_Entry__Size.v` | protobuf-generated `raftpb` code. The one a reader may want to argue about: a library in spirit, core raft in location |
| `wp_confchange_Restore` | `proof_confchange_Restore.v` | **core raft, not translated.** Voters-only `ConfState` onto the empty tracker; fresh config and progress maps. `voters ≠ []` is load-bearing: with no ops `Restore` returns the input maps themselves |
| `wp_ConfState__Equivalent` | `proof_ConfState__Equivalent.v` | **core raft (`raftpb`), not translated.** Only the `nil` outcome, for permuted voter lists and empty other lists |
| `wp_fmt_Sprintf`, `wp_strings_Join` | `proof_fmt_Sprintf.v`, `proof_strings_Join.v` | Go standard library, not translated. *Some* string; used only for `newRaft`'s log line |

### The admission signed off on for now

`proof_raftLog__slice.v` ends `Admitted. (* Trusted *)` for one arithmetic
side condition, `|ents| + |unstable| < 2^63` at the `extend` call: Go computes
`len(dst)+len(vals)` as an `int`, and with about `2^63` unstable entries it
wraps, so the triple is false there. The bound is not derivable — `is_Storage`
gives the stable part `< 2^61` and the model bounds any one slice at `2^63` —
and it can be neither carried (an append cannot re-establish a carried bound)
nor stated as a premise (nothing at `Step` can see the log's length). The
same admitted triple also asserts that the log comes back unchanged beside
a read-only result, which holds because the log holds its entries read-only
(`↦*□`, `inv_raftlog.v`) and never writes one again. It sits on the
`hup → hasUnappliedConfChanges → slice → extend` path, which cannot reach a
`Term`/`Vote` write.

### Two things the tool cannot see

- **A framework `Admitted` under the array proofs.** `into_val_typed_array`
  (`new/golang/theory/array.v`) is `Admitted` with three `admit`s;
  `wp_JointConfig__IDs` reads a `[2]MajorityConfig` through it. Outside the
  raft tree, so `tcb-report` does not count it.
- **`Print Assumptions` is not available as a cross-check.** Over a `.vos`
  tree it under-reports — it sees axioms reachable from *statements* but not
  what opaque proofs used. Ground truth needs a full `.vo` build of
  Perennial, which nothing in this tree has.

## Working on this

**Build state of this tree.** On branch `raft-phys-field-lemmas`
(2026-09-24, `own_raft_phys` sealed and every program proof converted to
its field lemmas): `.vok` of every file under `election_proof/` (helpers
included) plus `v3_proof/readonly.v` -- 333 targets -- passes, 0 errors.
Its base (`main` at `3bcd64960`, notes-only past `7703bd1f0`) passed the same 333.

**Checking your work.** `make <file>.vos` is a ~2s loop but **does not check
proof bodies** — it will accept a script that does not run. Use
`make <file>.vok` for the real check. Never claim a lemma is proved without
having seen `-vok` exit 0 on that revision. Do not reach for `.vo`: nothing
in the tree has `.vo` dependencies, so `make x.vo` starts building all of
Perennial.

**Writing against a big function.** Destructure the precondition before the
body is unfolded (`wp_start_folded as "@". iNamed "Hown". wp_start_unfold.`),
wrap a mid-body `iNamed`/`iNamedSuffix` in `wp_hidden (…)`, name the
field lemma for each raft-field access rather than searching for it, and do
not `set_solver` a list membership. Each is a 10–100× difference on `Step`; see
[gotchas.md](gotchas.md).

**Inner loop: rocq-warm**, specifically the
[upamanyus fork](https://github.com/upamanyus/rocq-warm), not zeldovich's.
Replays here are 0.3–30s, and a `Show.` to inspect a goal is an ordinary
replay rather than a cold check. Pass `--allow-stale`: this tree has `.vos`
only, and without it every check is refused with exit 2. **Exit 2 is not a
verdict** and neither is **exit 130** — a Ctrl+C or a killed client stops the
work but *keeps* the session, parked at the line it reached, so interrupting
a check you no longer want is cheap. A **git worktree is its own workspace**
(rocq-warm keys the daemon on `git rev-parse --show-toplevel`), so worktrees
do not share a session table or a memory budget, only the machine.
`--rebuild` will compile stale dependencies if you would rather not pass
`--allow-stale`. See [gotchas.md](gotchas.md).

For a file low in the dependency graph, `make <file>.vok` can beat rocq-warm
outright — `election_proof/protocol.v` sits directly on `proof_prelude` and checks
in 3–5s.

**On a machine with no Rocq**, budget ~16 min for the toolchain and ~1h
for a first `vo` build (measured 2026-09-30 on 24 cores; see below):

    sudo apt install opam build-essential m4 pkg-config libgmp-dev bubblewrap
    opam init --bare --disable-sandboxing
    opam repo add --all-switches rocq-released https://rocq-prover.org/opam/released
    opam repo add --all-switches core-dev https://rocq-prover.org/opam/core-dev
    opam switch create perennial ocaml-base-compiler.5.4.1
    eval "$(opam env --switch=perennial --set-switch)"
    opam install rocq-runtime.dev rocq-core.dev rocq-stdlib.dev
    opam pin add -n . && opam install --deps-only ./perennial.opam

The `core-dev` repo is what gives Rocq master (9.4+alpha), the version this
tree is developed against; without it opam picks stable 9.2.0 (gotchas.md).
Go 1.26.0 (CI's pin, for Goose) goes in `/usr/local/go`; `ruff` via
`uv tool install ruff==0.16.5`; rocq-warm per gotchas.md. **Check `opam
switch list` first**: on the machine this repo is usually worked on, Rocq is
installed in the `perennial` switch but not on a fresh shell's `PATH` —
`eval "$(opam env --switch=perennial --set-switch)"` (gotchas.md).

**Build times**, from scratch, `make -j24` on a 24-core / 94 GB box, Rocq
master `7751ff3ea`, tree at `e5bb0dc33` (2026-09-30):

| what | files | wall | CPU | avg cores |
|---|---|---|---|---|
| opam deps: OCaml 5.4.1 / Rocq core / stdlib / the five pins | — | 161 + 120 + 240 + 449 s ≈ 16 min | — | — |
| `election_proof/election.vo` and its whole closure, clean | 664 | 63 min | 4.7 h | 4.5 |
| `election_proof/` alone, everything below it built | 412 | 21 min | 2.7 h | 7.7 |
| `make ci` (`new/should_build.vo`), clean | 872 | 65 min | 6.0 h | 5.5 |

More cores would not help much: the builds are bound by their critical
paths, not by CPU. `make ci`'s was 3,738 s over 60 files, and five files
were most of it — `slices_proof/pdqSort/heapSort.v` (939 s, compiled alone
while everything waits), `election_proof/proof_raftLog__slice.v` (865 s),
`chan/au_spec/chan_au_recv.v` (289 s), `golang/theory/slice.v` (246 s) and
`election_proof/inv_raft_phys.v` (219 s).

**Since then (same machine, 2026-09-30)** the election proof's two slowest
idioms were replaced (gotchas.md, "Re-seal with an `_intro` lemma"):
`election_proof/` alone now rebuilds in **13 min** (was 21), its critical
path 653 s (was 1,156 s): `inv_raft_phys.v` 144 s → `proof_raftLog__slice.v`
374 s → … → `election.v`. The clean-closure and `make ci` rows above predate
that and were not re-measured; expect each to be ~8 min shorter, since the
saving is on their critical path too. Peak RSS of
any single `rocq compile` was 3.9 GB. `rocq dep` on the whole tree: 2 s.

**Every `make ci` now ends with a build report** — wall/CPU time,
parallelism over time, the critical path, slowest files — and CI puts it on
the run's summary page; `make build-report` reprints the latest. See
CONTRIBUTING.md, "Build reports". Use it before guessing where build time
goes.

**Memory.** `proof_raft__Step.v` and its helpers are the expensive part of
the tree; four at once peak around 8 GB, so `-j4` is the most a 15 GB box
should run beside nothing else.

## Before you add a claim

Statements in this development have been asserted, compiled, and lived in the
tree until a proof needed the fact and could not get it — including some with
a `Qed` resting on them. A plausible-looking bookkeeping claim about
`send`/`msgs`/`msgsAfterAppend` is the shape that keeps going wrong; check it
against `raft__sendⁱᵐᵖˡ` specifically. The table, the tells to grep for, and
the two-probe check for a pointer-receiver spec are in
[false-statements.md](false-statements.md). **Read it before writing a spec or
an `Admitted`.**

**An assumption you have not tried to prove is an assumption you have not
read carefully.**

## Standing facts

- `new/code/` and `new/generatedproof/` are Goose output. **Never edit them by
  hand** and never imitate their style. Regenerate with
  `new/etc/update-goose-new.py`.
- `make ci` builds `new/should_build.vo`, which is what CI checks. A proof not
  reachable from `new/should_build.v` is not being built.
- Faster inner loop: `make vos`, or
  `make new/proof/go_etcd_io/raft/v3.required_vos` to build just what a file
  depends on. See `CONTRIBUTING.md`.
- **Every build prints a per-file time** — a `ROCQ TIME <secs> <mode> <file>`
  line as each file finishes — and records it in `.timing.sqlite3`, keyed on
  the file *and* the build mode. `make timing-report` ranks the bottlenecks;
  `make TIMING_MIN=10` prints only the slow ones.
- Both python CI jobs must stay green: run `ruff check .` and
  `ruff format --check .` before pushing a change under `etc/` or `new/etc/`.
- The Go module path here is still `github.com/mit-pdos/perennial` and the
  Rocq logical paths are still `Perennial`/`New`, on purpose — see
  [decisions.md](decisions.md).
