# Extending the model past election: log replication, heartbeats, and beyond

**Started 2026-10-01**, branch `worktree-raft-replication`. This file is the
design the work is being done against; `STATUS.md` says how far it has got.
It is written for the agent doing a piece of it: read the section for your
piece, then the files it names.

## Goal

`wp_raft__Step` (`election_proof/spec_raft__Step.v`) is today stated only
for `MsgHup`/`MsgVote`/`MsgVoteResp`, against a protocol model
(`election_proof/protocol.v`) whose node state is
`(term, vote, lead, role, votes, outbox)`. The goal is to make `Step` a
verified spec for **every message type raft handles**, against a protocol
model whose transitions are the Raft protocol -- log replication (append,
heartbeat, commit, propose), then snapshots, then pre-vote,
reconfiguration and the read-index optimisation.

Two deliberate relaxations of the standing rules, both from the user
(2026-10-01):

- **`protocol.v` may contain `Admitted` lemmas.** The protocol-level
  obligations -- that `own_raft_ghost_step` preserves the ghost state for
  the new rules, and the safety consequences (log matching, leader
  completeness, state-machine safety) -- may be admitted while the
  implementation side is built. `tcb-report` counts them; they are debt,
  listed in STATUS.md.
- Everything below `Step` stays `Qed`, phys-only, and under the module
  discipline exactly as before. **No `Admitted` outside `protocol.v`**
  without a `(* Trusted *)` sign-off recorded in STATUS.md.

Order of work, from the user: (1) appending entries and heartbeats, (2)
snapshots, (3) pre-vote, reconfiguration, read-only.

## The three layers, unchanged

    Go code + heap  --own_raft_phys-->  nstate.t   (defs.v)
    nstate.t        --nstate_rel----->  pstate.t   (protocol.v)
    pstate.t        --own_raft_ghost->  protocol facts

`own_raft_phys cfg r id s` stays the one ownership predicate; every spec
below `Step` is on it; `Step` is the only spec that mentions ghost state.
See `notes/decisions.md` "Three layers" and `STATUS.md`.

## The protocol model (`protocol.v`), extended

### Entries

The protocol log is a list of **wire entries**, `raftpb.Entry.t`
(`new/code/go_etcd_io/raft/v3/raftpb.v`): `Term'`, `Index'`, `Type'`,
`Data' : slice.t`. `protocol.v` therefore `Require`s the generated
`raftpb` types file (types only, no code). Rationale: the physical log
(`logstate.t`, `inv_raftlog.v`) already holds `list raftpb.Entry.t`, so
`nstate_rel` on the log is equality, and the protocol's entry identity --
`(Index', Term')` -- is the one the Go code uses. `Data'` is a pointer the
model carries but never reads; the bytes are nobody's in the proof (the log
holds entries `↦*□`, nothing owns `Data'`'s contents).

Pure functions on `list raftpb.Entry.t` live in **`election_proof/plog.v`**
(new shared file, `Require`d by `protocol.v`; role `None` for
`check-module-discipline`):

    Definition ent_id (e) : raft.entryID.t := {| term := e.Term'; index := e.Index' |}
    (* well-formed log after base [b]: indices b.index+1, b.index+2, ... *)
    Definition plog_wf (b : raft.entryID.t) (es : list Entry.t) : Prop :=
      ∀ k e, es !! k = Some e → uint.Z e.Index' = uint.Z b.index' + S k.
    Definition plog_last (b) (es) : raft.entryID.t      (* last entry id, or [b] *)
    Definition plog_term_at (b) (es) (i : w64) : option w64   (* [term_at] of inv_storage.v, same shape *)
    Definition plog_matches (b) (es) (id : raft.entryID.t) : Prop :=
      plog_term_at b es id.index' = Some id.term'     (* raftLog.matchTerm *)
    Definition plog_find_conflict (b) (es) (ents : list Entry.t) : w64
      (* raftLog.findConflict: first index in [ents] whose term differs from ours or is past our end; 0 if none *)
    Definition plog_truncate_append (b) (es) (ents) : list Entry.t
      (* keep [es] up to (excluding) [ents[0].Index], then append [ents] -- unstable.truncateAndAppend's three arms, as one function *)
    Definition plog_up_to_date (b) (es) (their : raft.entryID.t) : bool
      (* raftLog.isUpToDate: their.term > last.term ∨ (their.term = last.term ∧ their.index ≥ last.index) *)

Write these so that **the `raftLog` specs can be stated with them**
(wave 1 below) and so that the model rules can use them; one definition,
two users.

### Abstract messages

    Module mtype.  Inductive t :=
      Vote | VoteResp | App | AppResp | Heartbeat | HeartbeatResp
      | Prop | Snap          (* Snap: phase 2 *)
      | PreVote | PreVoteResp | ReadIndex | ReadIndexResp.   (* phase 3 *)

    Module msg.  Record t := mk {
      ty : mtype.t; from to term : w64; reject : bool;
      index logterm commit rejecthint : w64;           (* Index, LogTerm, Commit, RejectHint *)
      entries : list raftpb.Entry.t;                   (* Entries, as a list *)
    }.

`from_leader ty` is true for `App | Heartbeat | Snap`.

**The abstraction is no longer pure.** `abs_msg ty m` (`defs.v`) cannot
produce `entries` from `m : raftpb.Message.t` (that is a `slice.t`). It
becomes `abs_msg ty m ents` with `ents` the list behind `m.Entries'`, and
`own_raft_phys` relates the two queues to the outbox with a *spatial*
relation in place of `Houtbox`'s `≡ₚ abs_outbox msgs msgsAA`:

    "Houtbox" ∷ outbox_rel s.(nstate.outbox) (msgs ++ msgsAA)
    (* ∃ abs, ⌜ s.outbox ≡ₚ abs ⌝ ∗ [∗ list] m;am ∈ (omap-filtered msgs++msgsAA);abs, msg_abs m am
       with msg_abs m am := ∃ ents, ⌜ am = abs_msg ty m ents ⌝ ∗ m.Entries' ↦*□ ents   (ty from mtype_of)
       and a message with mtype_of = None contributes nothing (MsgCheckQuorum etc.) *)

The entries points-to is persistent, so this is cheap to carry and to
duplicate. `send`'s spec (`spec_raft__send.v`) gains a parameter `ents`
and a premise `m.Entries' ↦*□ ents` (or `ents = []` with `m.Entries' =
slice.nil` for messages without entries -- `maybeSendAppend` builds a
`MsgApp` from the slice `raftLog.entries` returned `↦*□`). `send_ok` gains
clauses for every type raft sends; the three existing clauses keep their
shape. `own_raft_phys_msgs`/`_msgsAA` (`inv_raft_phys.v`) change
accordingly. **`Step`'s precondition** gets, next to `Hctx`,
`"#Hents" ∷ (∃ ents, m.Entries' ↦*□ ents ∗ …)` and `Hm` is stated with
that `ents`.

`mtype_of : w32 → option mtype.t` is extended (`MsgAppResp = 4`,
`MsgHeartbeatResp = 9`, `MsgProp = 2`, `MsgSnap = 7`, `MsgPreVote = 17`,
`MsgPreVoteResp = 18`, `MsgReadIndex = 15`, `MsgReadIndexResp = 16`;
see `raftpb.v:74-120`). **Consequence**: `MsgAppResp` now *has* an
abstraction, so `appendEntry`'s self-addressed `MsgAppResp` is in the
abstract outbox (the leader acknowledging its own append -- the model
needs it, see `step_propose`), and `spec_raft__appendEntry.v`'s
"unchanged outbox" postcondition changes to a one-message growth.

### Node state

    Module pstate.  Record t := mk {
      term vote lead : w64; role : role.t; votes : gmap w64 bool; outbox : list msg.t;
      base : raft.entryID.t;             (* logstate.prev: the compaction boundary *)
      log : list raftpb.Entry.t;         (* logstate.sents ++ logstate.uents *)
      commit : w64;                      (* logstate.committed *)
      match : gmap w64 w64;              (* each voter's Progress.Match, from nstate.prvals *)
    }.

`to_pstate s` (`defs.v`) computes all of these from `s : nstate.t`:
`base`/`log`/`commit` from `s.logst`, and
`match := (λ p, p.1.(tracker.Progress.Match')) <$> s.prvals`. **`nstate_rel`
stays `to_pstate s = ps ∧ nstate_wf s`** -- a function of the physical
state, as today.

Why `match` is in the protocol state: the leader's `maybeCommit` advances
`committed` to `trk.Committed()`, the quorum index over `Progress.Match`,
and a `step_commit` rule has to be able to say "a quorum has acknowledged
`N`". The acknowledgements arrive one `Step` at a time, so the knowledge
must be *state*, and the only honest place is the field the code reads.
Cost: specs that today return `<| nstate.prvals := pvs |>` with `pvs`
unconstrained must now say what happened to `Match` (see "Match
discipline" below). `applied` is physical only; no rule reads it.

### Rules

Existing rules keep their names. Changes:

- `step_higher_term` unchanged (already adopts `from` as leader for
  `from_leader` types).
- `step_grant_vote` gains the premise
  `plog_up_to_date s.base s.log (m.logterm, m.index) = true`. Leader
  completeness depends on it; it was invisible while the model had no
  log. (`isUpToDate` stays "may decline" -- `step_reject_vote` has no
  premise -- but a *grant* now records that the check passed.)
- `step_campaign`'s `Vote` messages carry the candidate's last entry id
  in `logterm`/`index` (the code: `campaign` sends `Index: last.index,
  LogTerm: last.term`).
- `step_win`'s broadcast premise `app_sends` is replaced by
  `Forall (app_ok cfg id s') ms` (below).
- `pbecome_*` keep `base`/`log`/`commit`; `pbecome_leader` is followed, in
  the implementation, by the empty entry: `step_win` appends
  `leader_entry` (the zero `Entry` stamped `term`, `last+1`) -- today
  `become_leader` (defs.v) already does, and the model must too (it did not
  need to while the model had no log). The non-leader `pbecome_*` take the
  new `match` as an argument (irrelevant for a non-leader; the physical
  values are whatever `reset` left); `pbecome_leader` sets
  `match := {[ id := plog_last.index ]}` with every other voter at `0` --
  that is what `reset` does (`raft.go:779-808`: `Match: 0` for all,
  `pr.Match = lastIndex()` for self).

New rules (all with `m.to = id`; all message terms equal to `s.term`
because `step_higher_term` has already run):

- `step_app_accept m s`: `m.ty = App`, `s.role ≠ Leader`,
  `plog_matches base log (m.logterm, m.index)`. Result: `lead := m.from`,
  `role := Follower`, `votes := ∅`
  (a candidate reaches this through `becomeFollower(m.Term, m.From)`, a
  follower through `r.lead = m.From`; the two agree on `pstate` because a
  follower's `votes` are always `∅`), `log := plog_truncate_append …`
  (only when `plog_find_conflict ≠ 0`; the model should use one function
  `plog_maybe_append` that returns the new log), `commit := max commit
  (min m.commit lastnewi)` with `lastnewi = m.index + |m.entries|`, outbox
  `++ [AppResp id m.from s.term index:=lastnewi reject:=false]`.
  **Premise** `ci = 0 ∨ ci > s.commit` where `ci` is the conflict index
  (the code `Panicf`s otherwise; the protocol must guarantee it -- a
  protocol lemma, admitted if necessary, see "Protocol facts the code
  needs").
- `step_app_stale m s`: `m.ty = App`, `m.index < s.commit`. Adopt the
  leader as above; outbox `++ [AppResp … index:=s.commit reject:=false]`.
- `step_app_reject m s hint hintterm`: `m.ty = App`, `m.index ≥ s.commit`,
  `¬ plog_matches …`. Adopt the leader; outbox `++ [AppResp … index:=m.index
  reject:=true rejecthint:=hint logterm:=hintterm]` for **any** `hint`,
  `hintterm` (they are an optimisation; pinning them is not needed for
  safety and would need `findConflictByTerm` pinned).
- `step_heartbeat m s`: `m.ty = Heartbeat`, `s.role ≠ Leader`. Adopt the
  leader; `commit := max commit m.commit`; outbox `++ [HeartbeatResp id
  m.from s.term]`. **Premise** `m.commit ≤ (plog_last base log).index`
  (`commitTo` `Panicf`s otherwise; protocol fact).
- `step_beat s ms`: `s.role = Leader`; outbox `++ ms` with
  `Forall (λ m, m.ty = Heartbeat ∧ m.from = id ∧ m.term = s.term ∧ m.to ≠ id
  ∧ uint.Z m.commit ≤ uint.Z s.commit ∧ uint.Z m.commit ≤ match_of s m.to) ms`
  (`sendHeartbeat`: `Commit: min(pr.Match, committed)`).
- `step_app_resp m s`: `m.ty = AppResp`, `s.role = Leader`, `¬ m.reject`:
  `match := <[m.from := max (match m.from) m.index]>` (`MaybeUpdate`).
  Followed, in the same `Step`, by zero or more of `step_commit`,
  `step_send_apps`. A **rejecting** `AppResp` changes no protocol state
  (`MaybeDecrTo` moves `Next`, not `Match`); it may `step_send_apps`.
- `step_commit s N`: `s.role = Leader`, `s.commit < N ≤ last.index`,
  `plog_term_at base log N = Some s.term`,
  `is_quorum cfg {[ v | N ≤ match v ]}` (the leader's own `match` entry
  counts; `reset` sets it to `lastIndex` and the self-`AppResp` from
  `appendEntry` keeps it current). `commit := N`.
- `step_send_apps s ms`: `s.role = Leader`, outbox `++ ms`,
  `Forall (app_ok cfg id s) ms` where

      app_ok cfg id s m := m.ty = App ∧ m.from = id ∧ m.term = s.term ∧ m.to ≠ id
        ∧ plog_term_at s.base s.log m.index = Some m.logterm
        ∧ m.entries = sub-list of s.log starting right after index m.index (a prefix of that suffix)
        ∧ uint.Z m.commit ≤ uint.Z s.commit

  (`maybeSendAppend`: `Index: pr.Next-1, LogTerm: term(pr.Next-1),
  Entries: entries(pr.Next, maxMsgSize), Commit: committed`.)
- `step_propose s ents`: `s.role = Leader`, `ents` all `EntryNormal`
  (phase 1 scope: no conf change proposed; `EntryConfChange` is phase 3),
  `log := log ++ stamped ents` (`stamp s.term last`, `defs.v`),
  `match := <[id := new last]>` is **not** done here -- the code acks
  itself by message: outbox `++ [AppResp id id s.term index:=newlast
  reject:=false]` (`appendEntry`'s self-send, which `Step(MsgAppResp)`
  later turns into `step_app_resp`). Followed by `step_send_apps`.
  **Dropped proposals** (`increaseUncommittedSize` rejects, no leader,
  leader transfer) are `step_refl` with `err = ErrProposalDropped` -- the
  `Step` spec's `err = nil` conclusion becomes `err = nil ∨ (m.Type = MsgProp
  ∧ err = ErrProposalDropped)`.
- `step_prop_forward m s`: `s.role = Follower`, `s.lead ≠ 0`: outbox `++
  [m with to := s.lead]` (the message is forwarded with `Term = 0`,
  `send`'s `MsgProp` exception). A candidate or leaderless follower drops
  it: `step_refl`, `ErrProposalDropped`.
- `step_drain`, `step_refl`, `step_trans` unchanged.
- Phase 2: `step_snap m s` (`handleSnapshot`/`restore`: `base := (index,
  term)`, `log := []`, `commit := index`, or the `matchTerm` fast-forward
  `commit := index`; reply `AppResp`). Phase 3: pre-vote, conf change,
  read index. Design them when phase 1 is in.

### Ghost state and `is_message`

Keep the vote ghost maps. Add, per node, a ghost map `term ↦ gname` of
**per-term log authorities** (`is_term_log γ id t γt`, frozen): the node
that becomes leader in `t` allocates a `mono_list` of entries for `t` --
at most one node per term is leader (`is_leader_unique`) and a node is
leader in a given term at most once, so the authority is exclusive by
construction, no invariant. Then:

- `is_entry γ t e` -- "the leader of `t` has `e` in its log" (a
  `mono_list_idx_own` under `is_term_log`). Log Matching is agreement of
  two `is_entry`s at one `(t, index)`.
- `is_acked γ v t i` -- "`v`'s log agreed with the leader-of-`t`'s log up
  to `i`" (per-node frozen fact, like `is_vote`).
- `is_committed γ t i` -- a quorum of `is_acked … t i'` with `i ≤ i'`.
- `is_message γ m`: `App` carries `is_leader γ m.from m.term`, `is_entry`
  for every entry and for the prefix id, and `is_committed γ m.term
  m.commit`; `AppResp` (grant) carries `is_acked γ m.from m.term m.index`;
  `Heartbeat` carries `is_leader` and `is_committed`; `VoteResp` as today.
- `own_raft_ghost` additionally holds: `is_entry` for every entry of its
  log under the leader of that entry's term (every entry a node has came
  from some leader); `is_acked γ v s.term (match v)` for each `v` when
  `role = Leader`; `is_committed … s.commit`.

`own_raft_ghost_step` is proved case by case; **the new cases may be
`Admitted`**, each as its own `Local Lemma` so the admitted set is
legible in `tcb-report`. The safety statements -- `log_matching`,
`leader_completeness`, `state_machine_safety` -- are stated in
`protocol.v` as lemmas over the ghost assertions and may be admitted.
Say in each admit's comment what the informal argument is.

**As built, replication-safety pass (2026-10-02).** The design above with
these changes (`protocol.v`, "Logs as persistent knowledge" and
"Acknowledgements, justified"):

- `is_term_log γ v t γt b l0`: the term log also records the leader's
  base `b` and log `l0` at its win; the term log (`γt : index ↦ (entry,
  prevterm)`) holds only entries created in `t`, each with its
  predecessor's term. `is_entry_r γ e pt`; `is_entry γ e := ∃ pt, …`.
- `own_log_ghost` gained `log_ok` (`plog_wf_r` -- well-formed *in range*,
  since `step_win` can wrap at `lastIndex() = 2^64-1` -- and `base ≤
  commit ≤ lastIndex()`), `log_recs` (every entry's `is_entry_r` with its
  predecessor's term *in this log*), `acks_term` (acks only at one's own
  term) and `acks_ok` (a non-leader's acks of its current term above its
  commit index are `ack_agree`: the log agrees at `i` with a
  `lead_prefix` of that term's leader). `lead_log_own` also keeps `l0 ⊑
  log` and a term-log fragment for each entry after `l0`.
- `is_message`: `App` carries `∃ bL l, lead_prefix from term bL l ∗
  ⌜(logterm, index) ∈ l ∧ entries ⊑ l after index⌝` (replacing the
  per-entry `is_entry`s); `Snap` the same for `(logterm, index)`;
  `Heartbeat` `∃ i ≥ Commit, is_acked to term i`.
- No rule changed. `log_matching`, `heartbeat_commit_le_last` and
  `app_no_conflict_below_commit` are `Qed`; `leader_completeness` and
  `state_machine_safety` are not provable from two nodes' ghost state
  (their comments: a third node's votes/acks are unconstrained) and stay
  admitted with the remaining obligation spelled out.

### Protocol facts the code needs

Several `Panicf`/`panic` paths in the replication code are dead only by
protocol reasoning. A callee's spec (phys-only, by the rule) takes the
fact as a **premise**; `Step` discharges it from `own_raft_ghost` and the
incoming `is_message` using a lemma from `protocol.v`, admitted if
necessary:

| code | fact | lemma in `protocol.v` |
|---|---|---|
| `commitTo`: `lastIndex() < tocommit` | a leader's `Commit` in an `App`/`Heartbeat` the node *accepts* is `≤` its last index after the append | `heartbeat_commit_le_last`, `app_commit_le_lastnewi` |
| `maybeAppend`: `ci ≤ l.committed` | an accepted `App` never conflicts below the commit index | `app_no_conflict_below_commit` |
| `maybeAppend`: `ci-offset > len(entries)` | arithmetic; provable from `plog_find_conflict`'s definition | pure |
| `raftLog.append`: `after < committed` | same as the conflict fact | same |

Each premise is stated on `pstate`/`plog` terms so it can be derived once.

## The implementation side

### Match discipline (phase 1, before anything leader-side)

Every spec whose postcondition has `<| nstate.prvals := pvs |>` with an
unconstrained `pvs` must now pin `Match`. Add a pure postcondition:

    ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝     (* Match untouched *)

with `prvals_match pvs := (λ p, p.1.(tracker.Progress.Match')) <$> pvs`
(`defs.v`), or, for `reset`,

    ⌜ prvals_match pvs = (λ _, W64 0) <$> s.prvals  with  id ↦ log_last s.logst ⌝

Affected (`grep -l "prvals := pvs" election_proof/spec_*.v`):
`reset`, `becomeFollower`, `becomeCandidate`, `becomeLeader`, `hup`,
`campaign`, `stepCandidate_MsgVoteResp`, `bcastAppend`, `sendAppend`,
`maybeSendAppend`, `maybeSendSnapshot`, `ProgressTracker__Visit`(closure),
plus `Progress__*` specs whose `∃ pv' iv'` must say `pv'.Match = pv.Match`
(`SentEntries`, `SentCommit`, `BecomeReplicate`, `BecomeSnapshot`,
`ResetState`). Callers destructure the extra conjunct; `to_pstate_prvals`
(`defs.v`) becomes a lemma about `prvals_match`.

### Phys-level specs: statements, not sketches

A spec must be checked against the generated body before it is written
down (`notes/false-statements.md`). The pattern that keeps going wrong is a
claim about `send`/queues; the second is a `Panicf` assumed away. For
every new collection:

1. read `raft__<fn>ⁱᵐᵖˡ` in `new/code/go_etcd_io/raft/v3.v` (line numbers in
   STATUS.md's table or `grep -n "Definition raft__<fn>ⁱᵐᵖˡ"`), and the Go
   in `raft.go`/`log.go` for intent;
2. list every exit and every panic; each panic needs a premise that makes
   it dead, derivable by the caller;
3. state the postcondition at the *new* `nstate.t`/`logstate.t`, by the
   pure functions of `plog.v`/`defs.v`, never "some state".

The log functions (`raftLog.*`) are stated on `own_raftLog l ls` and
`logstate.t`; the raft methods on `own_raft_phys cfg r id s`; the tracker
methods on `own_progress`/`own_tracker`. Reaching into the struct is only
through the `inv_raft_phys.v` interface (`wp_raft_load_<f>`, accessors);
see `proof_raft__maybeSendAppend.v` for borrowing a `Progress` and the log
around a `send`.

### Collections to add (phase 1)

Wave 1 -- log and tracker level, no `send`, independent of the model
change (so they can be built in parallel with it):

| function | spec, in one line |
|---|---|
| `raftLog.term` (widen) | returns `t` with `plog_term_at prev (sents++uents) i = Some t` when in range; needs `unstable.maybeTerm` to pin `t` and `is_Storage`'s `HTerm` (`term_at`) |
| `unstable.maybeTerm` (widen) | `ok → t = (uents !! (i - offset)).Term'` |
| `raftLog.lastEntryID` (widen) | returns `plog_last prev (sents++uents)` |
| `raftLog.isUpToDate` (widen) | `b = plog_up_to_date …` |
| `raftLog.matchTerm` (new) | `b = bool_decide (plog_matches …)` |
| `raftLog.findConflict` (new) | takes `es ↦*{dq} ents`, returns `plog_find_conflict …`; `Infof` on the way |
| `raftLog.findConflictByTerm` (new) | returns *some* `(i', t')` with `i' ≤ index`; no more is needed |
| `raftLog.zeroTermOnOutOfBounds` (new) | pure on its arguments |
| `raftLog.commitTo` (new) | premise `tocommit ≤ last`; `committed := max` |
| `raftLog.maybeCommit` (new) | `at.term ≠ 0 ∧ at.index > committed ∧ matches → committed := at.index, true`; else false |
| `unstable.truncateAndAppend` (widen to 3 arms) | result `plog_truncate_append` at the unstable level; the replace/truncate arms adopt or copy the caller's slice -- see `raft-implementation-facts.md` "uncapped slices" |
| `raftLog.append` (widen) | drop the continuation premise; result `plog_truncate_append` |
| `raftLog.maybeAppend` (new) | the follower's whole decision: `(lastnewi, ok)`, log and `committed` as `step_app_accept` says; premises = the two panics' facts |
| `Progress.MaybeUpdate` | `Match := max`, `Next := max Next (n+1)`, returns `n > Match` |
| `Progress.MaybeDecrTo` | `Match` unchanged; returns a bool; `Next`/`sentCommit` as the body |
| `Progress.BecomeProbe` | `Match` unchanged; `State := Probe` |
| `Progress.CanBumpCommit` | pure on `pv` |
| `Inflights.FreeLE` | `own_inflights` at *some* new `iv` with `count ≤` old; nothing reads more |
| `ProgressTracker.Committed` | returns the quorum index of `Match` over voters: `is_quorum cfg {[v | N ≤ match v]}` for the result `N`, and `N` is some voter's `Match` -- via `MajorityConfig.CommittedIndex` (`slices.Sort` is an axiom already) and `JointConfig.CommittedIndex` (second config empty → `MaxUint64`, `min`) |
| `pbEntryID`, `logSliceFromMsgApp` | pure |

Wave 2 -- after the model lands (they mention `send`'s new `send_ok` or the
new `to_pstate`):

`raft.handleAppendEntries`, `raft.handleHeartbeat`, `raft.sendHeartbeat`,
`raft.bcastHeartbeatWithCtx`, `raft.bcastHeartbeat` (needs
`readOnly.heartbeatCtx`: with no pending reads it returns `nil`),
`raft.maybeCommit`, `raft.appendEntry` (widen: arbitrary `EntryNormal`
batch; the drop path), `stepFollower` (widen: `MsgApp`, `MsgHeartbeat`,
`MsgProp`, and the arms that are dead under scope), `stepCandidate`
(widen), `stepLeader` (widen: `MsgBeat`, `MsgAppResp`, `MsgHeartbeatResp`,
`MsgProp`), then the `Step` branches
`proof_raft__Step_helpers/proof_raft__Step_{MsgApp,MsgHeartbeat,MsgAppResp,MsgHeartbeatResp,MsgBeat,MsgProp}.v`
and the dispatch in `proof_raft__Step.v`.

### Scope for phase 1

Unchanged from STATUS.md except: `MsgApp`, `MsgAppResp`, `MsgHeartbeat`,
`MsgHeartbeatResp`, `MsgBeat`, `MsgProp` are now received. Still assumed:
no pre-vote, no check-quorum, no learners, no conf change (`EntryNormal`
only, also in proposals), no snapshot received (phase 2), no leader
transfer, `readOnly.option = ReadOnlySafe` with no read requests (so
`heartbeatCtx` is `nil` and a `MsgHeartbeatResp` with empty `Context`
returns before the read-only code), `disableProposalForwarding = false`.

## Working in parallel

Several agents work at once, **each in its own git worktree**, on
disjoint collections; the coordinator merges. A fresh worktree has no
build artifacts; the main checkout at `/home/ubuntu/etcd-grove` has a full
`.vo` build of `e5bb0dc33`. To make a worktree at that commit buildable
without compiling:

    rsync -a --include='*/' --include='*.vo' --include='*.glob' --exclude='*' /home/ubuntu/etcd-grove/new/ new/
    rsync -a --include='*/' --include='*.vo' --include='*.glob' --exclude='*' /home/ubuntu/etcd-grove/src/ src/
    cp -p /home/ubuntu/etcd-grove/.rocqdeps.d .
    python3 /home/ubuntu/.claude/jobs/9dcc9726/tmp/mkmarkers.py .    # empty .vos/.vok beside each .vo, then touch all
    export PATH=/home/ubuntu/.opam/perennial/bin:$PATH

(`mkmarkers.py`: for every `.vo` create empty `.vos`/`.vok`; `utime` every
`.vo/.vos/.vok/.glob` and `.rocqdeps.d` to now. An empty `.vos` tells
`rocq -vos` to load the `.vo`.) Then `make <file>.vo` compiles only
`<file>` and whatever you changed; a leaf file is ~15 s. Check with
`.vo` (full check) rather than `.vok`; there is no reason to use `.vos`
here. Do not run `make` with no target, and do not run two `make`s at
once in one worktree (the `.rocqdeps.d` regeneration races).

## Public representation predicates (requested 2026-10-02)

The tracker-side predicates leak the Goose struct types into every spec:
`own_progress pr (pv : tracker.Progress.t) (iv : tracker.Inflights.t)`,
`own_inflights l iv buf`, `own_tracker cfg tv votes prs pvs` with
`pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t)`, and
`nstate.prvals` of the same type. Specs of exported methods then say
`pv.(tracker.Progress.State') = W64 1`, pin ring-buffer fields nobody
outside `Inflights` reads, and take four or five arguments where one record
would do. The rule, from the user: **a public predicate per object, indexed
by one record of exactly the state the exported methods' specs need; an
internal predicate, with the extra arguments, for the object's own
methods.** Spec-oriented records, not `Progress.t`/`Inflights.t`/
`ProgressTracker.t`.

### Records (`inv_tracker.v`)

    Module inflights.
      Record t := mk { count : Z; size : Z; bytes : Z; max_bytes : Z }.
      Definition full (i : t) : bool := bool_decide (count = size) || (max_bytes ≠ 0 && max_bytes ≤ bytes).
      Definition reset (i : t) : t := i <| count := 0 |> <| bytes := 0 |>.   (* Inflights.reset *)
      (* Add, FreeLE as functions where the result is determined; FreeLE's result
         is "count' ≤ count, bytes' arbitrary" -- stated as a relation. *)
    Module pstate_kind. Inductive t := Probe | Replicate | Snapshot.   (* StateType, as an inductive *)
    Module progress.
      Record t := mk {
        matched : w64; next : w64; sent_commit : w64;
        state : pstate_kind.t; pending_snapshot : w64;
        recent_active : bool; paused : bool;            (* MsgAppFlowPaused *)
        infl : inflights.t }.
      (* pure versions of every exported method: maybe_update, maybe_decr_to,
         become_probe, become_replicate, become_snapshot, is_paused, sent_entries,
         sent_commit, can_bump_commit, reset_state -- moved from the spec files
         where the tracker agent defined them (progress_maybe_update, ...). *)
    Module trk.   (* [tracker] is the Goose module's name *)
      Record t := mk { votes : gmap w64 bool; prs : gmap w64 loc; peers : gmap w64 progress.t }.

`IsLearner = false` and `progress_state_ok` disappear into the record (no
learner field; the state is an inductive), so the two pure conjuncts of
today's `own_progress` go.

### Predicates

    own_Inflights (l : loc) (i : inflights.t) : iProp :=
      ∃ iv buf, own_inflights l iv buf ∗ ⌜ inflights_abs iv = i ⌝          (* public *)
    own_inflights l iv buf                                                   (* internal; grow, Add's ring arithmetic *)
    own_Progress (pr : loc) (p : progress.t) : iProp :=
      ∃ pv, pr ↦ pv ∗ own_Inflights pv.Inflights' p.infl ∗ ⌜ progress_abs pv = Some p ⌝   (* public *)
    own_tracker cfg (tv : tracker.ProgressTracker.t) (t : trk.t)             (* indexed by one record *)

`progress_abs pv : option progress.t` is `None` when `IsLearner` or the
state is not one of the three; the predicate then says exactly what the two
old pure conjuncts said. `prs` stays in the tracker record because callers
hold a raw `*Progress` across `send` (`maybeSendAppend`) and the
`own_raft_phys_pr` accessors are keyed by it; it is physical state, like
`nstate.log`.

### Where it lands

- `nstate.prvals : gmap w64 progress.t` (was `gmap w64 (Progress.t * Inflights.t)`);
  `prvals_match pvs := progress.matched <$> pvs`; `nstate.votes`,
  `nstate.progress`, `nstate.prvals` stay separate fields, and
  `own_raft_phys` passes `{| votes := s.votes; prs := s.progress; peers := s.prvals |}`
  to `own_tracker`.
- Every `spec_Progress__*.v` and `spec_Inflights__{Full,Add,FreeLE,reset}.v`
  is restated on `own_Progress` / `own_Inflights` with the pure function of
  the record; `Inflights__grow` stays on the internal predicate.
- `spec_ProgressTracker__*`, `spec_raft__{reset,maybeSendAppend,maybeSendSnapshot,sendAppend,bcastAppend,sendHeartbeat,bcastHeartbeat*,becomeLeader}`,
  `spec_stepLeader.v`, `inv_raft_phys.v`'s accessors
  (`own_raft_phys_pr*`, `_tracker*`), `visit_closure`, `own_progress_map`
  (fold it into `own_tracker` or define it on the record) follow.
- The pure functions the tracker agent put in spec files
  (`progress_maybe_update`, `progress_maybe_decr_to`, `progress_become_probe*`)
  move into `inv_tracker.v` on `progress.t`.

Sequencing: after the heartbeat/leader and follower branches of 2026-10-01
are merged (they are stated on the old predicates), before the `Step`
branches of wave 3, so that wave 3 is written against the final shapes.

## Phase 2: snapshots (design, 2026-10-02; model side done 2026-10-02)

What the code does (`raft.go:1827-1932`, `log.go:464`, `log_unstable.go`
`restore`): `handleSnapshot` reads `*m.Snapshot` (nil → the zero
`Snapshot`), calls `restore(s)` and replies `MsgAppResp{Index:
lastIndex()}` on success or `MsgAppResp{Index: committed}` otherwise.
`restore` returns `false` when `s.Metadata.Index ≤ committed`; when the
node is not a follower (dead under our scope: both callers run after
`becomeFollower`); when `r.id` is in none of the `ConfState`'s sets
(dead under the fixed voter set, `id ∈ cfg`); and when
`matchTerm (s.Metadata.Term, s.Metadata.Index)` holds, in which case it
only `commitTo(s.Metadata.Index)`. Otherwise `raftLog.restore`:
`committed := index`, `unstable.offset := index + 1`, `unstable.entries :=
nil`, **`unstable.snapshot := &s`**; then the tracker is rebuilt from the
`ConfState` (`MakeProgressTracker`, `confchange.Restore`, `switchToConfig`,
`assertConfStatesEquivalent` -- all specified for `newRaft` already).

### What has to change

- **`own_raftLog` / `logstate.t`.** `Hnosnap` (`unstable.snapshot = null`)
  is a scope conjunct today. A received snapshot sets the pointer, and it
  stays set until `MsgStorageAppendResp` (out of scope) calls
  `stableSnapTo`. So `logstate.t` gains `snap : option raft.entryID.t`
  (the pending snapshot's `(term, index)`), `own_raftLog` owns
  `unstable.snapshot ↦□ snap` when `Some`, and the index facts become:
  with a pending snapshot the visible log is `prev = snap.id`, `sents = []`
  (storage is shadowed below `offset = index + 1`), `uents` as before.
  `firstIndex`/`lastIndex`/`term`/`maybeTerm` have snapshot arms
  (`log_unstable.go:40-80`); their specs stay as stated on `prev`/`sents`/
  `uents` -- only the proofs gain a case.
- **`promotable`** becomes `b = bool_decide (id ∈ cfg ∧ snap = None)`
  (`hasNextOrInProgressSnapshot`); `hup`/`campaign` take `snap = None`
  from the state (a node with a pending snapshot does not campaign).
- **`raftLog.snapshot()`** returns the pending one first; `maybeSendSnapshot`
  (leader side, already proved) needs the new arm.
- **Model.** `pstate.t` needs no new field: `base := (term, index)`,
  `log := []`, `commit := index`. Rule:

      step_snap m s : m.ty = Snap → m.to = id → m.term = s.term → s.role ≠ Leader →
        (uint.Z s.commit < uint.Z m.index) →
        ¬ plog_matches s.base s.log (mk m.logterm m.index) →
        step s [m] (psend_msgs (padopt_leader s m.from
                      <| base := mk m.logterm m.index |> <| log := [] |> <| commit := m.index |>)
                    [AppResp id m.from s.term false m.index …])
      step_snap_fastfwd …: plog_matches → commit := m.index, reply AppResp(m.index)
      step_snap_stale …:   m.index ≤ s.commit → reply AppResp(s.commit)

  The abstract `Snap` message carries `index`/`logterm` := the snapshot
  metadata (`abs_msg` must read them through `m.Snapshot ↦□ snap`, so the
  outbox relation gets a `Snap` case like `App`'s entries), and
  `is_message` for `Snap` carries `is_committed γ m.index` plus
  `is_entry`-like knowledge of `(index, term)` -- the leader sends a
  snapshot only of its applied (hence committed) prefix. The receiver's
  ghost update (`own_raft_ghost_step_snap`) replaces its whole log by the
  committed prefix: provable from log matching once that is proved;
  admit it meanwhile.
- **`ConfState`.** Under the fixed-voter-set scope the snapshot's
  `ConfState` is `cfg`'s voters (a transport premise of `Step` for
  `MsgSnap`: `cs.Voters ≡ₚ elements cfg`, no learners, no outgoing);
  `confchange.Restore`'s axiom and `switchToConfig`'s spec already cover
  that case (`newRaft`). Reconfiguration proper is phase 3.
- **Sender side.** `maybeSendSnapshot` is proved for the `Storage.Snapshot`
  path; `snap_ok` (protocol.v) says only who sent it. It gains
  `m.index ≤ s.commit` and the metadata facts once the message abstraction
  carries them.

Order of work: `logstate.snap` and the log proofs' snapshot arms (one
agent; invalidates the cone), then `handleSnapshot`/`restore` as
collections, `stepFollower`/`stepCandidate` `MsgSnap` arms, the `Step`
branch, the model rule and ghost update.

### Done 2026-10-02: the model and message side

What is in (`protocol.v`, `defs.v`, `inv_raft_phys.v`, `spec/proof_raft__send.v`,
`spec/proof_raft__maybeSendSnapshot.v`, `spec/proof_raft__Step.v`):

- **`msg.t` has a field `voters : list w64`** (a `Snap`'s
  `ConfState.Voters`, `[]` otherwise). The constructor is now `msg.mk_v`
  (11 fields); `msg.mk` is an *abbreviation* (`Notation`) for `mk_v … []`,
  so every ten-argument `msg.mk` in the tree is unchanged and still a
  literal constructor application.
- **`abs_snap m sv voters`** (`defs.v`, with `abs_snap_from m from term sv
  voters` for `send`'s stamped form): `ty := Snap`, `index`/`logterm` :=
  `sv.Metadata.Index`/`.Term`, `entries := []`, `voters`, the rest from `m`.
  `abs_msg` is unchanged and is not used for `MsgSnap`. `mtype_of_Snap`:
  only `MsgSnap` maps to `Snap`.
- **`msg_abs`** (`inv_raft_phys.v`) has three cases: undescribed;
  described-and-not-`Snap` (`abs_msg`, entries `↦*□`); `MsgSnap` with
  `∃ sv voters, a = Some (abs_snap m sv voters)` -- **pure, not tied to the
  heap**. Deviation from the brief, for two reasons: `send` (the only
  producer of `msg_abs`) has no precondition carrying `m.Snapshot ↦□ sv`,
  and adding one adds a goal at every `send` call site, including the
  `Step` helpers (off-limits during the concurrent merge); and
  `maybeSendSnapshot` could not supply `ConfState.Voters ↦*□ voters` anyway
  (`raftLog.snapshot`'s spec returns the snapshot by value, `HSnapshot`
  gives no ownership). Tying it: add `"#Hsnap"` to `send`'s precondition
  (one bullet per caller), and voters ownership to `HSnapshot` +
  `spec_raftLog__snapshot.v`.
- **`send_ok`**: clause (b) is now `MsgApp | MsgHeartbeat | MsgReadIndexResp
  | MsgHeartbeatResp` (`MsgReadIndexResp` takes the same body path and keeps
  the third slot so `by right; right; right` still means `HeartbeatResp`);
  the old clause (c) became `(c') ∨ (c)` with (c') `MsgSnap ∧ Term = 0 ∧
  To ≠ id ∧ ∃ sv voters, out = [abs_snap_from m id s.term sv voters]` --
  no caller used (c), so no caller's clause selection moved.
- **`snap_ok`** gained only `m.index ≠ 0` (from `HSnapshot`). `m.index ≤
  s.commit` is **not derivable**: `HSnapshot` does not relate the
  snapshot to `applied`/the log, and `raftLog.snapshot` passes it on
  verbatim. `maybeSendSnapshot` sends `abs_snap_from m id term snap []`
  (`snap` the storage's snapshot; voters `[]`, unpinned).
- **`is_message` for `Snap`**: `is_leader γ from term ∗ is_committed γ index ∗
  is_snap_meta γ logterm index`, with `is_snap_meta γ t i := ∃ e, is_entry γ
  e ∗ ⌜e.Term = t ∧ e.Index = i⌝` -- defined through `is_entry`, no new
  ghost state, so it agrees with log entries by `is_entry_agree`.
  The sender's side is **`snap_ok_message` (Admitted)**: a client
  assumption about `Storage`, not a protocol fact (see its comment).
- **Rules** `step_snap_restore`, `step_snap_fastfwd`, `step_snap_stale`
  (premises: `Snap`, `to = id`, `from ≠ id`, `term = s.term`, role ≠
  Leader; restore/fastfwd also `voters ≡ₚ elements cfg`, `id ∈ cfg`,
  `commit < index`, and `¬`/`plog_matches base log (logterm, index)`;
  stale `index ≤ commit`). All adopt the leader (`padopt_leader`) and reply
  `AppResp(reject = false)` at `index` (restore, fastfwd) or `s.commit`
  (stale), as `handleSnapshot` does. **All three ghost updates are Qed**:
  `own_log_ghost` holds nothing about `base`, so a restore needs only
  `is_committed index` (the message's) and the node's own ack.
- **`Step`'s spec**: `Hm`'s `Hmsg` is `∀ ty, mtype_of = Some ty -∗ ty ≠ Snap
  -∗ is_message (abs_msg ty m ents)`; new pure premise `MsgSnap → To = id ∧
  Term ≠ 0 ∧ From ≠ 0 ∧ From ≠ id`; new `"#Hsnap" ∷ □ (⌜Type = MsgSnap⌝ -∗
  ∃ sv voters, m.Snapshot ↦□ sv ∗ sv…ConfState.Voters ↦*□ voters ∗ ⌜voters
  ≡ₚ elements cfg⌝ ∗ ⌜Learners/VotersOutgoing/LearnersNext have len 0⌝ ∗
  is_message γ (abs_snap m sv voters))`. `step_msg` is **not** widened; the
  proof rebuilds the old `Hmsg` (Snap is not in `step_msg`) and clears
  `Hsnap`.

**Next, for the log-side agent**: `logstate.snap` and the log proofs'
snapshot arms; `raftLog.restore`, `raft.restore`, `raft.handleSnapshot`
specs (replies as in the rules above; `restore`'s `found` loop needs `id ∈
voters`, from `voters ≡ₚ elements cfg` and `id ∈ cfg`;
`confchange.Restore` needs `0 ∉ voters` -- from `cfg`, check where that is
known -- and the three empty sets `Hsnap` gives); `stepFollower`/
`stepCandidate` `MsgSnap` arms; then add `MsgSnap` to `step_msg_types`, a
`dispatch_Snap` in `proof_raft__Step.v` destructing `"Hsnap"` and the
`Hsnapt` premise, choosing among the three rules. Separately (sender
fidelity): voters ownership and the applied bound in `HSnapshot` +
`raftLog.snapshot`'s spec, then `snap_ok` gains `m.index ≤ s.commit` and
`snap_ok_message` can be proved (with a `base` fact in `own_log_ghost`
for a compacted index).

## Phase 3: pre-vote, reconfiguration, read-only (scoping, 2026-10-02; not started)

In the user's order. Each lifts one `own_raft_phys` scope conjunct, so each
is a cone-wide change; none has been designed in detail yet, and the model
rules below are sketches to be checked against the bodies first
(`notes/false-statements.md`).

### Pre-vote (`preVote = true`)

Code (`raft.go`): `hup(campaignPreElection)` → `campaign` →
`becomePreCandidate` (step := stepCandidate, votes reset, `lead := 0`,
`state := StatePreCandidate`; **term and vote unchanged**) and sends
`MsgPreVote` with `Term: r.Term + 1` (`campaign` sends at `term = r.Term+1`
for pre-vote, `raft.go:1030-1040`). Receiver (`Step`): a `MsgPreVote` with a
higher term does **not** step the node down (`raft.go:1102`); `canVote`
gains the disjunct `m.Type == MsgPreVote && m.Term > r.Term` and the
`inLease` check (`checkQuorum`, still false) is skipped; a granted
`MsgPreVoteResp` carries the *future* term and does not record a vote;
a rejecting `MsgPreVoteResp` at a higher term makes the receiver step
down (`raft.go:1104`); a stale `MsgPreVote` is answered with a rejecting
`MsgPreVoteResp` at the receiver's term (`raft.go:1144-1152`).
`stepCandidate`: `myVoteRespType` is `MsgPreVoteResp` in `StatePreCandidate`,
and winning runs `campaign(campaignElection)`, i.e. the real election.

Model: `role.t` gains `PreCandidate` (`StatePreCandidate = 3`,
`step_func_of` = `stepCandidate`); `pstate.votes` is reused for the
pre-vote tally; rules `step_precampaign` (no term change; sends `PreVote`
at `term+1`), `step_grant_prevote`/`step_reject_prevote` (no state change
besides the send; granting needs the up-to-date check and
`m.term > s.term`), `step_record_prevote`, `step_prewin` (quorum of
pre-votes → `step_campaign`), `step_prelose` (→ follower). Ghost: a
pre-vote grant is **free** (`is_message` trivial): it records nothing, so
election safety is untouched; the model only has to let the code do what
it does. Costs: `own_raft_phys`'s `HnoPreVote` goes (the field becomes
`nstate.prevote : bool` or a `cfg`-like parameter); `Step`'s preamble
proofs gain the `MsgPreVote`/`MsgPreVoteResp` arms (every existing branch
re-checks); `campaign`, `hup`, `becomePreCandidate` (new), `poll`
(`voteRespMsgType` for `MsgPreVote`), `stepCandidate` (the
`StatePreCandidate` branch, incl. the win → `campaign` path), `tickElection`
unchanged. `newRaft` copies `c.PreVote`.

### Reconfiguration

Code: a leader's `MsgProp` with `EntryConfChange`/`EntryConfChangeV2`
entries (`raft.go:1296-1330`: `pendingConfIndex`, the "already pending"/
joint checks, `traceChangeConfEvent`); the entry is replicated like any
other; **application** happens through `RawNode`/`node` calling
`ApplyConfChange` → `raft.applyConfChange` (`raft.go:1939`) →
`confchange.Changer.{Simple,EnterJoint,LeaveJoint}` → `switchToConfig`,
which may change the voter set, add learners, remove the node itself
(`Progress[r.id] == nil` → a leader stops proposing), and transfers
leadership on leaving a joint config. `hasUnappliedConfChanges` guards
`hup`.

Model: `cfg` stops being a parameter. The protocol state carries the
configuration (`voters : gset w64`, possibly `outgoing` for joint
consensus) and `step_win`/`step_commit`/`is_quorum` are relative to it;
`is_leader γ id term` must say which configuration elected it, and
election safety becomes the joint-consensus argument (quorums of both the
incoming and outgoing configuration). That is a second protocol proof of
the size of the election one. Costs on the implementation side: translate
`confchange` (today `translate = ["Changer"]` only; `Restore` and
`Equivalent` are axioms), drop `HnoConfChange` from `own_raftLog` in
favour of "no conf change in `(applied, committed]`" (STATUS item 2),
`own_tracker` over a joint `Config` (`Voters[1]`, `Learners`,
`LearnersNext`, `AutoLeave`), `applyConfChange`/`switchToConfig` for real
configs, `own_raft_phys_reconfig` becomes an ordinary transition, and the
entry point `ApplyConfChange` is on `RawNode`, outside `Step` -- so the
development needs its first spec above `Step` (STATUS item 3 is the same
boundary). Suggested order: entries of type `EntryConfChange` allowed in
the log first (the `MsgProp` loop's scope premise lifted; application
still out of scope), then `applyConfChange` with the voter set as state,
then joint consensus.

### Read-only (`ReadOnlySafe`)

Code: `MsgReadIndex` at the leader (`raft.go:1346-1360`): singleton →
answer immediately; no entry committed in the current term → queue in
`pendingReadIndexMessages`; else `sendMsgReadIndexResponse` →
`readOnly.addRequest(committed, m)`, self-ack, `bcastHeartbeat` with a
non-empty `heartbeatCtx`; `MsgHeartbeatResp` with a `Context` →
`recvAck`, `maybeAdvance` → `responseToReadIndexReq` (a `ReadState` for a
local request, `MsgReadIndexResp` for a forwarded one);
`releasePendingReadIndexMessages` after a commit; a follower forwards
`MsgReadIndex` to its leader and turns `MsgReadIndexResp` into a
`ReadState`. The old `v3_proof/readonly.v` development is the protocol for
exactly this (heartbeat contexts, acknowledgement quorums, `is_read_index`)
and is the thing to reconcile with `protocol.v` (STATUS item 6).

Model: the read index is a linearizability claim, not a safety-of-log
claim: "`readIndex` ≤ the commit index of every later leader" follows from
leader completeness plus a quorum of heartbeat acknowledgements in the
leader's term. Rules: `step_readindex_queue`, `step_readindex_start`
(heartbeat with context), `step_readindex_ack`, `step_readindex_resolve`
(a quorum of acks for a context → `ReadState (readIndex, ctx)` or a
`ReadIndexResp`). Costs: `own_read_only` gets real state (`acks`,
`unconfirmedReads` as a queue of `(index, ctx, req)`), `own_raft_misc`'s
`readStates`/`pendingReadIndexMessages` become indexed state, the
heartbeat specs carry the context, `heartbeatCtx`'s `nil` result is no
longer the only case, `MsgHeartbeatResp`'s empty-`Context` premise goes,
and `readOnly.{addRequest,recvAck,maybeAdvance,AckedIndex}`,
`responseToReadIndexReq`, `sendMsgReadIndexResponse`,
`committedEntryInCurrentTerm`, `ProgressTracker.IsSingleton` get
collections. `maybeAdvance` hands out an uncapped sub-slice of
`unconfirmedReads` (raft-implementation-facts.md); its one caller only
ranges over it.
