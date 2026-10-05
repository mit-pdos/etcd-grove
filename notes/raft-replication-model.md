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

**As built, leader-completeness pass (2026-10-03/05).** Both safety
theorems are `Qed`, stated over the cluster; `protocol.v` has no
`Admitted`. Changes (all in `protocol.v` unless said):

- **Model**: `step_win` gained the premise `lastIndex() + 1 < 2^64`
  (the code's `own_raftLog` `Hnowrap`; discharged in
  `proof_raft__Step_MsgVoteResp.v`, threaded through
  `step_record_then_win` in `step_lemmas.v`). Without it Leader
  Completeness is *false* in the model: a leader that wrapped its log has
  last id `(T, 0)`, votes for any candidate with last term `T`, and a
  3-node counterexample loses a committed entry.
- **Full logs** ("Full logs", before `Section model`): a node's log
  `(b, es)` has a ghost compacted prefix `fp` (`full_ok b fp`: entries
  `1..b.index`, ending in `b`), with records; Leader Completeness compares
  full logs `fp ++ es` from `base0`, so snapshots are no special case.
  `lpfull`/`lead_full γ t G` carry the leader's full log next to
  `lead_prefix`.
- **Campaign records** (`re_camp`, `is_camp γ c T F`, frozen at
  `step_campaign`, `camp_ok`: well-formed, every term `< T`); a `Vote`
  request carries the candidate's (`is_message`); a candidate's full log
  is it, a leader's extends it (`camp_own`). `is_entry_r` now also names
  the camp of the entry's term and `pt_ok`: the entry is past the camp's
  end, follows its last entry or one of its own term, `pt ≤ term` (so
  record-carrying logs have non-decreasing terms, `recs_mono`, and
  `recs_chain` walks an entry of term `T` down to where `T`'s leader
  started).
- **Commit facts name the log**: `cq γ t n G` (quorum acks of `t` at
  `≥ n`, `G` a `lead_full` of `t` with term `t` at `n`), `commit_in γ F c
  tm` (`F` agrees with such a `G`, `t ≤ tm`, at `c`); a node keeps
  `commit_in` of its commit index, `App`/`Heartbeat`/`Snap` carry it of
  what they report; `is_committed` is derived. Messages from a leader
  also carry `from ≠ 0`.
- **Histories**: `hist γ F t i B` -- at each `j ≤ i`, `F` has what some
  `okL` log has (a `lead_full` of a term in `[t, B)`, or a committed log of
  an earlier term), or two such logs already disagree at or below `j`.
  Every ack has its history for the current full log at bound `bnd s`
  (the term, `+1` once the node has a leader or is one); a log change
  keeps it (`hist_keep`, `hist_replace` for the cut of `step_app_accept`
  and `step_snap_restore`).
- **Vote records**: each vote `T ↦ c` in `voted` has `vote_just`: an
  `is_vlog` (new map `re_vlogs`) naming the voter's full log `Fv` at vote
  time, `c`'s camp, `Fv`'s records and `up_to_date(Fv, last camp)`;
  `vlogs_ok` keeps, for each vote-time log, the history of every earlier
  ack at bound `T` (a first vote is cast with `bnd s = term`).
  `role_ok` (non-follower → voted for itself; candidate → no leader) is
  new in `own_raft_ghost`.
- **Theorems**: `cluster_ghost γ S := ⌜dom S = re_cfg⌝ ∗ [∗ map] id ↦ ps
  ∈ S, own_raft_ghost γ id ps`. `lc_core` (induction on the leader's
  term): a `cq t n F`, `t < T`, puts term `t` at `n` in every recorded log
  reaching the end of `T`'s camp. `leader_completeness` /
  `state_machine_safety` (cluster, primary) follow with
  `commit_in_leader`, `cq_agree`. The receiver lemmas' statements are
  unchanged.

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

### `readonly.t` (2026-10-04)

The read-only object got the same treatment: `own_ReadOnly ro (r : readonly.t)`
(`inv_misc.v`, public; replaces `own_read_only`), with `readonly.t := {safe :
bool; pending : list readreq.t; acks : gmap w64 w64; confirmed : w64}` and
`readreq.t := {index; from; ents : list raftpb.Entry.t}` (the part of a queued
`readIndexRequest` anyone reads back: `responseToReadIndexReq` uses
`req.From` and `req.Entries`).  The records and the pure functions
(`readonly_add/recvAck/advance/position`) live at the top of `inv_misc.v`, not
`defs.v`: a `defs.v` edit rebuilds the log and tracker cone.  Inside:
the struct, the acks map, the queue held `↦*□` with only the slack owned
(`own_slice_cap`), and each request `own_readreq p q` (persistent).
`own_raft_misc` keeps `pending = []` as its phase-1 conjunct (phase 3 lifts
it); `own_raft_phys_readOnly` hands the object out at a record with
`pending = []` and takes it back at any such record.  `maybeAdvance`'s
uncapped result is specified as `sl ↦*□ ptrs` plus `own_readreq` of the
dropped records, with no capacity: no loan.  `acks` is indexed by *position*
(the heartbeat context, `confirmed + len pending`), not by index.  Premises
added for panics the state cannot exclude: `recvAck` needs `ctx = [] ∨ 8 ≤
len`; `maybeAdvance` needs a non-empty voter set and every voter's ack `≤
confirmed + len pending`.  `JointConfig.CommittedIndex` was *not* general over the indexer
(its spec was fixed to `matchAckIndexer` on `own_tracker`): it is now the
general triple (receiver `c ↦ a`, `a = [m0; nil]`, any `is_AckedIndexer`), and
`ProgressTracker.Committed` instantiates it (its proof lifts the `Voters`
field's location out of `trk ↦ tv` with two `access_strict`s).

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

## Phase 3: pre-vote, reconfiguration, read-only (scoping, 2026-10-02; pre-vote done 2026-10-04)

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

**Model (decided with the user, 2026-10-04): pre-vote is an implementation
detail; the protocol does not model it.** Nothing a pre-vote does touches
protocol state: `becomePreCandidate` leaves `Term` and `Vote` alone, sets
`lead := 0`, resets the physical tally and swaps `r.step`; a granted
`MsgPreVote` records nothing on either side; a `MsgPreVoteResp` leads only
to the real `campaign` (already `step_campaign`) or to `becomeFollower`.
So:

- `is_message` for `PreVote`/`PreVoteResp` stays `True` (they are already
  in `mtype.t`); `pstate.role` is unchanged.
- `nstate.role` gains the **physical** constructor `PreCandidate`
  (`state_w64 = 3`, `step_func_of = stepCandidate`); `to_pstate` maps it to
  `role.Follower` with `lead := 0` and `votes := ∅` (the pre-vote tally in
  `trk.Votes` is invisible to the protocol; `follower_votes_ok` holds).
- Two trivial rules: `step_send_free s m` (`msg_free m.ty = true` → outbox
  `++ [m]`: a `PreVote` at `term+1`, a `PreVoteResp` either way) and
  `step_abandon s` (a candidate that times out and pre-campaigns is,
  protocol-wise, a follower at the same term keeping its vote). Both
  preserve every ghost conjunct trivially: no vote is granted, no leader is
  created. A rejecting `MsgPreVoteResp` at a higher term is
  `step_higher_term` with a non-leader message, as today.

Costs are all implementation-side: lift `HnoPreVote` from `own_raft_phys`
(`nstate.prevote : bool`, or a parameter like `cfg`); collections
`becomePreCandidate`, and the `StatePreCandidate` arms of `campaign`
(`MsgPreVote` at `Term+1`), `hup`, `poll`/`voteRespMsgType`,
`stepCandidate` (`myVoteRespType`, win → `campaign(campaignElection)`);
`Step`'s preamble arms for `MsgPreVote` (never steps down; `canVote`'s
third disjunct) and `MsgPreVoteResp` (step down only when rejecting at a
higher term), and the stale-term rejecting `MsgPreVoteResp`. Every existing
`Step` branch re-checks (the `preVote` loads stop being constant), but no
refinement argument changes. `newRaft` copies `c.PreVote`.

#### Done 2026-10-04: pre-vote, as planned (plus one rule)

Branch `worktree-agent-a55b1ab28ca9c10e1` (from `1e5c18fce`).  All `Qed`
outside `protocol.v`; `make -k -j4 …/election.vo` green; module discipline
3 warnings (unchanged); `tcb-report --scope election_proof`: 14 `Axiom`, 3
`Admitted`, 605 `Qed`, 130 collections.

- **Physical state** (`defs.v`).  `nstate.role : prole.t`
  (`Follower | Candidate | Leader | PreCandidate`; `pstate.role` is still
  `role.t`), `state_w64 PreCandidate = W64 3`, `step_func_of PreCandidate =
  stepCandidate`, `prole_role` (a pre-candidate is a `role.Follower`).
  `to_pstate` reads `lead := if PreCandidate then 0 else lead`, `role :=
  prole_role role`, `votes := if PreCandidate then ∅ else votes` (the
  pre-vote tally is invisible).  `nstate.prevote : bool` is `r.preVote`
  (`own_raft_phys`'s `Hprevote`, replacing `HnoPreVote`;
  `wp_raft_load_preVote` returns it); `newRaft` copies `Config.PreVote`
  and its spec no longer assumes `false`.  `become_precandidate` (role,
  `lead := 0`, `votes := ∅`, `stepfn`; term/vote/`Progress` untouched),
  `to_pstate_become_precandidate : to_pstate (become_precandidate s) =
  pbecome_follower (to_pstate s) s.term 0`, `prevote_req`,
  `campaign_state id s pre peers`.  Lemmas `to_pstate_votes` (now needs
  `role ≠ PreCandidate`), `to_pstate_votes_pre`, `to_pstate_lead_0`,
  `follower_votes_ok_phys`.
- **Collections.**  New `raft.becomePreCandidate` (premise `role ≠
  Leader`).  `campaign(t)` returns `campaign_state … (bool_decide (t =
  campaignPreElection)) peers` and covers `promotable`'s warning (the
  `snap = None` premise went: the pre-vote win calls `campaign` without
  it).  `hup` takes any `t`.  `voteRespMsgType` is relational (`Vote ↦
  VoteResp`, `PreVote ↦ PreVoteResp`).  `send_ok` clause (a) has the two
  pre-vote types.  `stepCandidate`: role `Candidate ∨ PreCandidate`; a
  `MsgVoteResp` at a pre-candidate is a no-op, a `MsgPreVoteResp` at a
  candidate too; at a pre-candidate `precand_vote_resp_result` /
  `prevote_resp_result` (win = `campaign_state … false`, lose =
  `become_follower s1 term 0`).  `stepFollower`/`stepLeader` take
  `MsgPreVoteResp` as a no-op (it reaches `r.step` in any role).
- **`Step`.**  Twelve types.  New premises: `MsgPreVote` -- `To = id`,
  `Term ≠ 0`, `From ≠ 0`, `From ≠ id`, and **at term `0` the candidate is
  up to date**: a higher-term pre-vote is rejected at the node's own term,
  `send` panics on `Term = 0`, and nothing in `own_raft_phys` relates the
  term to the log (a persisted log ahead of the persisted term would make
  `Step` panic; etcd never builds one).  `MsgPreVoteResp` -- `To = id`,
  `Term ≠ 0`, `From ≠ 0`, term no-wrap.  Branches
  `proof_raft__Step_MsgPreVote{,_gt,_eq,_lt}.v` (always `step_send_free`;
  `canVote` is evaluated under a `wp_wand` join) and
  `proof_raft__Step_MsgPreVoteResp{,_gt,_eq,_lt}.v` (rejecting higher
  term: `step_higher_term`; else per role, the pre-candidate by
  `step_prevote_resp_result`); pure lemmas in
  `proof_raft__Step_prevote_lemmas.v`.  Every existing helper re-checked:
  the role destructs got a `PreCandidate` bullet (stepCandidate, as the
  candidate), the stale-term helpers split on `prevote`.
- **Stale-term `MsgAppResp`.**  With pre-vote on, `MsgApp`/`MsgHeartbeat`
  of a lower term are answered with `MsgAppResp{To: m.From}` (`Index = 0`,
  stamped `Term`).  `is_acked γ v t 0` holds for free (its first
  disjunct), so `is_message` is satisfiable, but no rule sent an `AppResp`
  outside the replication rules: a **third rule**, `step_zero_ack s to`
  (outbox `++ [AppResp id to term false 0 0 0 0 []]`), was added.
- **Rules** (appended to `step`, ghost cases `Qed`): `step_send_free s m`
  (premise `ty = PreVote ∨ ty = PreVoteResp` and `from = id` -- `msg_free`
  is defined after `step`, with the ghost state, so it could not be the
  premise), `step_abandon s` (premise `role ≠ Leader`, not `= Candidate`:
  a *follower* that pre-campaigns forgets its leader, which no other rule
  allows), `step_zero_ack s to`.

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

### Done 2026-10-02: the log and implementation side (`Step` takes `MsgSnap`)

Branch `worktree-agent-a6ef9862e0d3133ee` (from `c0edb8a9f`).  All `Qed`
outside `protocol.v` (untouched).  What landed, in the order it was built:

- **`logstate.snap : option entryID`** (`defs.v`), the pending snapshot.
  `own_raftLog_core lv snap prev sents uents` (`inv_raftlog.v`) now
  quantifies the storage's own boundary `sprev` with `stored`, related to
  the visible log by `log_store_ok snap sprev stored prev sents uents`:
  `None` -- `sprev = prev`, `sents` a prefix of `stored`, all of it when
  `uents = []` (the old `Hstored`/`Hstored_eq`); `Some sid` -- `prev = sid`,
  `sents = []`, `0 < sid.index < 2^61`, the storage **shadowed** (never
  asked: `firstIndex`/`lastIndex` answer from the snapshot arms, `term`
  answers `i < sid.index` with `ErrCompacted` and `i = sid.index` from
  `maybeTerm`, `slice` starts at `firstIndex = offset`).  The snapshot cell
  is `own_snap u.snapshot snap` -- **sealed** (`own_snap_None`/`_Some`
  open it), because an unfolded instance stops `own_raftLog_intro` from
  inferring `snap`.  `prev.index <= applied` holds only for `snap = None`
  (a restore leaves `applied` below the new boundary); `prev.index <=
  committed` always.  `to_pstate` is unchanged (`base := prev`).
- Log proofs: `unstable.maybeFirstIndex/maybeLastIndex/maybeTerm` take
  `own_snap` and cover the snapshot arms (`maybeTerm` needs `offset =
  sid.index + 1`); `raftLog.firstIndex/lastIndex/term/snapshot/slice`
  prove theirs; `hasNextOrInProgressSnapshot` returns `snap ≠ None`.  New
  collections `unstable.restore` (stores `&s`, a fresh cell, persisted) and
  `raftLog.restore` (`log_restore ls sid := mk sid [] [] sid.index applied
  (Some sid)`; premises `committed < index < 2^61`).
- **`promotable = id ∈ cfg ∧ snap = None`**; `hup` passes `snap = None` to
  `hasUnappliedConfChanges` and `campaign` (both gained the premise: with a
  pending snapshot `applied` may lie below the boundary and `scan` would
  `Panicf`).  `hup`'s spec did not change.
- **`raft.restore`** (`restore_result`) and **`raft.handleSnapshot`**
  (`handle_snap_result`): one disjunct per live exit -- obsolete (reply
  `AppResp(committed)`), fast-forward (`matchTerm` holds: `commitTo(Index)`,
  reply `AppResp(Index)`), restore (`raftLog.restore`, tracker rebuilt,
  reply `AppResp(lastIndex() = Index)`).  Premises: `role = Follower`,
  `votes = ∅` (the fresh tracker's `Votes` is empty and `nstate.votes`
  must not move), `id ∈ cfg`, and `snap_scope cfg sv voters`
  (`spec_raft__restore.v`): `voters ≡ₚ elements cfg`, `0 ∉ cfg`, no
  learners/outgoing/learnersNext, `AutoLeave = false`, `Index < 2^61`.
  The tracker rebuild goes through the empty configuration as in
  `newRaft`, with a new accessor **`own_raft_phys_retrack`**
  (`inv_raft_phys.v`): the `trk` and `raftLog` fields and the log out
  together, back at any configuration/tracker/log state -- needed because
  `restore` stores the fresh tracker, loads it back and calls
  `lastIndex()` *before* `confchange.Restore` takes the tracker's voter map,
  and re-sealing in between would forget which tracker value the struct
  holds.
- **`stepFollower`/`stepCandidate` `MsgSnap` arms**: two new binders
  `sv voters`, a precondition conjunct `"Hsnap" ∷ (⌜MsgSnap⌝ -∗ ⌜scope …⌝
  ∗ m.Snapshot ↦□ sv ∗ Voters ↦*□ voters)` (the follower's pure part also
  `role = Follower ∧ votes = ∅ ∧ id ∈ cfg`), the type premise's tail is
  `(Beat ∨ AppResp ∨ HeartbeatResp) ∨ Snap`, the result relations take `sv`
  (one more argument everywhere).  Callers with another type pass
  `(zero_val _) []` and discharge `"Hsnap"` with `step_no_snap`
  (`spec_stepFollower.v`).
- **`Step`**: `step_msg_types` has `MsgSnap`; `"Hsnap"`'s pure part is now
  `snap_scope cfg sv voters` (it adds `0 ∉ cfg`, `AutoLeave = false` and
  the index bound to what the model side had); branch
  `proof_raft__Step_helpers/proof_raft__Step_MsgSnap{,_gt,_lt,_eq}.v`;
  `dispatch_Snap` derives "not a leader at the message's term" from
  `is_leader_unique` and the follower's empty tally from
  `follower_votes_ok`; `step_handle_snap` (repl lemmas) maps the three
  exits to `step_snap_stale/_fastfwd/_restore`.  No protocol fact is
  needed beyond those: no `Panicf` is reachable (`commitTo` in the
  fast-forward is in range by `matchTerm`; a restore replaces the log).
  No rule needed changing.

Still open on the snapshot path after that: the sender side (done next,
below), and `stableSnapTo`/`Ready` (a pending snapshot is never cleared in
scope).

### Done 2026-10-03: the sender side (both deviations above removed)

Branch `worktree-agent-a4805cdd87b17c9a2` (from `1de11b38d`).  All `Qed`
outside `protocol.v`; **`snap_ok_message` is `Qed`** (protocol.v's
admits are down to `leader_completeness`/`state_machine_safety`).

- **The Storage contract pins the snapshot by naming it, not by bounding
  it.**  `own_Storage st prev ents ss` gained a fourth index, `ss :
  entryID`, the storage's current snapshot metadata (`MemoryStorage.snapshot`).
  `HSnapshot`'s success case: `snap_id snap = ss`, `Index ≠ 0` (as before),
  and `∃ voters, snap.Metadata.ConfState.Voters ↦*□ voters` (read-only, for
  good, like `Entries`).  Why not "`Index ≤ applied`" or "a stored entry id
  at or below …": a `Storage` does not know raft's `committed`/`applied`,
  and any *pure* parameter standing for them is satisfiable only vacuously
  (the client must meet it for every value the premise allows, e.g.
  `applied = prev.index`, which forces `Index = prev.index` -- false for
  etcd, which keeps catch-up entries after the snapshot).  So "the
  snapshot is of a committed prefix" is **raft's invariant**, not the
  storage's: `own_raftLog_core` gained `"%Hssnap" ∷ snap = None →
  stored_snap_ok ss committed prev (sents ++ uents)` (`inv_raftlog.v`):
  `ss.index = 0`, or `ss.index ≤ committed ∧ plog_term_at prev log
  ss.index = Some ss.term`.  Established at `newLogWithSize` by a new
  premise `ss.index = 0 ∨ ss = prev` (also on `newRaft`: fresh storage, or
  the `ApplySnapshot`-then-`Append` restart path; excluded: restarting on a
  storage whose snapshot is above its first index); preserved because the
  storage never changes in scope, `commitTo` only grows `committed`
  (`stored_snap_ok_commit`), and `append` rewrites only above `committed`
  (`plog_term_at_truncate_append_below`).
- **`own_snap`** (pending snapshot) also holds `∃ voters, Voters ↦*□ voters`;
  `unstable.restore`/`raftLog.restore` take it (binder `voters`), and
  `raft.restore` passes its `"#Hvoters"`.
- **`raftLog.snapshot`'s spec**: `err = esu`, or `nil` with `Index ≠ 0`,
  `Index ≤ committed`, `plog_term_at prev (sents ++ uents) Index = Some
  Term`, and the voters' `↦*□`.  Pending arm: the snapshot is the base.
- **`msg_abs`'s `MsgSnap` case** is `∃ sv voters, ⌜mtype_of = Some Snap ∧ a
  = Some (abs_snap m sv voters)⌝ ∗ m.Snapshot ↦□ sv ∗ sv…Voters ↦*□ voters`.
  **`send`** has a new conjunct `"#Hsnap" ∷ □ (⌜Type = MsgSnap⌝ -∗ ∃ sv
  voters, ⌜out = [abs_snap_from m id s.term sv voters]⌝ ∗ m.Snapshot ↦□ sv
  ∗ Voters ↦*□ voters)`; `send_ok`'s (c') lost its `∃ sv voters, out =`
  (the precondition fixes `out` now, for the heap's `sv`/`voters`).  Other
  callers discharge it with `send_no_snap` (`inv_raft_phys.v`), one
  `iSplitR` at 21 call sites (6 in the `Step` helpers).
- **`maybeSendSnapshot`** persists the local `snapshot` cell (`iPersist`)
  before the `send` -- `&snapshot` escapes into the queue and nobody
  writes it again.
- **Model**: `snap_ok` gained `index ≤ commit ∧ plog_term_at base log
  index = Some logterm`.  `own_log_ghost` gained `"#Hbase" ∷ base_ok γ
  base` (`base.index = 0 ∨ is_snap_meta γ base.term base.index`); only
  `step_snap_restore` moves the base, and the message's `is_snap_meta`
  re-establishes it.  `snap_ok_message` (premises `plog_wf_r`, `snap_ok`,
  `is_committed commit`, `log_recs`, `base_ok`) is then `is_committed_le`
  plus either `base_ok` (snapshot at the base, the usual case after
  `Compact`) or the log record of the entry at `index`.

## As built, 2026-10-05: the safety theorems over the cluster

`leader_completeness γ S id1 ps1 id2 ps2 i e` and `state_machine_safety γ S
id1 ps1 id2 ps2 i` take `cluster_ghost γ S` (every voter's
`own_raft_ghost`) and conclude, for an entry `e` committed at `id1`
(`i ≤ ps1.commit`, above both bases), that a leader `id2` at a term `≥
ps1.term` has `e` at `i`, resp. that two nodes' committed prefixes agree at
`i`. Proved by `lc_core`, an induction on terms, from the per-node history
invariants described in STATUS.md item 5b. The statements over two nodes'
ghost states alone are unprovable (journal, 2026-10-02): the argument needs
the pivot voter's own records. `protocol.v` has no `Admitted` left.

## As built: the global committed log (2026-10-05)

The external face of commitment: clients see one global authoritative log.

**Public predicates** (`protocol.v`, "The global committed log"; both sealed):

    is_committed γ (l : list raftpb.Entry.t)   (* mono_list_lb_own γ.(re_commit) l: l is a prefix of the global log *)
    own_committed γ l                         (* mono_list_auth_own γ.(re_commit) 1 l: the global log is l *)

    is_committed_pers / is_committed_timeless / own_committed_timeless
    is_committed_agree  : is_committed γ l1 -∗ is_committed γ l2 -∗ ⌜l1 ⊑ l2 ∨ l2 ⊑ l1⌝
    own_committed_lb    : own_committed γ l -∗ is_committed γ l
    is_committed_prefix : is_committed γ l -∗ own_committed γ l' -∗ ⌜l ⊑ l'⌝
    is_committed_mono   : l1 ⊑ l2 → is_committed γ l2 -∗ is_committed γ l1

The authority is held **whole** by the invariant (coordinator's correction
of the same day): `step_commit` extends it inside a leader's `Step`, with
no client involved, so no half can be outside. `is_committed` is the only
client-facing resource. The old index-valued `is_committed γ i` is now
`is_committed_idx` (internal; `snap_ok_message` and `own_log_ghost_committed`
use it).

**The invariant** (persistent, carried inside `own_log_ghost` as `Hinv`):

    raft_commit_inv γ := inv raftN (∃ l, own_committed γ l ∗ committed_just γ l ∗ votes_tbl γ)
    committed_just γ l := ⌜l = []⌝ ∨ ∃ t n G, cq γ t n G ∗ ⌜l = take n G⌝

`cq γ t n G` (unchanged since 2026-10-03) is the justification: `G` is a
full log of the leader of `t` (`lead_full`: its `is_win`, `lead_prefix`,
`lpfull`), with an entry of term `t` at `n`, and a quorum of `is_acked … t
i'` with `i' ≥ n`. `votes_tbl γ` holds **half of every node's vote map**
with each vote's `vote_just`; the node holds the other half
(`own_raft_ghost`'s `Hvoted` is `(1/2)` now; `own_raft_ghost_excl` uses the
term-log map instead).

**Why the vote table, and the event history.** Extending the global log
needs Leader Completeness / agreement of two commit facts (`cq_agree`),
which needs the pivot voter's records. These used to be read from the
pivot's own ghost state, hence `cluster_ghost`. Now:
- the vote record comes from `votes_tbl` (`votes_tbl_just`);
- the history of the pivot's acknowledgement at vote time comes from a new
  per-node **event history** `re_evs` (a `mono_list` of `aev = AAck t i |
  AVote T d F`, in term order): `is_acked` carries `ack_ev` (the ack is in a
  sorted lower bound), `vote_just` carries `vote_ev` (the vote is the last
  event of a lower bound, with `hist` of every earlier ack of a lower
  term), and `ev_pair` combines them. `own_log_ghost` gained `own_evs` (the
  authority, sorted, terms ≤ the node's, acks in the ack map).
So `lc_core`, `cq_lt_agree`, `cq_agree` take `votes_tbl γ` instead of
`cluster_ghost γ S` (`tbl_voter` replaces `own_raft_ghost_voter` /
`cluster_voter`), and the same section was moved before the step lemmas.

**`is_message`** — App, Heartbeat and Snap each gained one conjunct inside
their existing existentials:
- App: `∃ bL l fp, lead_prefix … ∗ ⌜…⌝ ∗ lpfull … fp ∗ commit_in γ (fp ++ l) Commit term ∗ is_committed γ (take Commit (fp ++ l))`
- Heartbeat: `∃ Fl, lead_full γ term Fl ∗ commit_in γ Fl Commit term ∗ is_committed γ (take Commit Fl)`
- Snap: `∃ bL l fp, … ∗ commit_in γ (fp ++ l) Index term ∗ is_committed γ (take Index (fp ++ l))`
(the committed prefix as entries, including the compacted prefix `fp`).

**`own_raft_ghost`** keeps (in `own_log_ghost`) `Hcmt : is_committed γ
(cprefix fp s)`, `cprefix fp s := take commit (fp ++ log)`. Exported:
`own_raft_ghost_committed : own_raft_ghost γ id s -∗ ∃ fp, ⌜full_ok s.base
fp⌝ ∗ is_committed γ (take commit (fp ++ s.log))` and `own_raft_ghost_inv`.

**Which steps touch the global log.** Only `step_commit` extends it:
`own_raft_ghost_step_commit` (now `={⊤}=∗`) builds `cq γ term n (fp ++
log)` from the leader's `Match` quorum and calls `commit_extend`, which
opens the invariant: the stored log is `take n0 G0` of an earlier `cq`;
`cq_agree` (over the table) makes `G0` and `G` agree in terms up to
`min n0 n`, `full_take_eq` (records ⇒ same entries) makes the prefixes
equal there, so either the global log is extended to `take n G`
(`mono_list_auth_own_update`) or it is already past it. Followers' commit
moves take `is_committed` from the message: `step_app_accept` (the new log
agrees with the leader's up to `lastnewi`), `step_heartbeat` (the ack the
heartbeat carries, `ack_agree`), `step_snap_fastfwd` (the log has the
snapshot's entry), `step_snap_restore` (the new compacted prefix is the
leader's). `step_win`/`step_propose` append past the commit index
(`cprefix_app`). Votes (`step_campaign`, `step_grant_vote`) open the
invariant to record the vote in the table (`vote_insert`).

**Allocation**: `own_raft_ghost_alloc E cfg ids : ⊢ |={E}=> ∃ γ, ⌜re_cfg =
cfg⌝ ∗ raft_commit_inv γ ∗ is_committed γ [] ∗ [∗ set] id ∈ ids,
own_raft_ghost γ id init_pstate` — no authority leaves the invariant.

**Safety theorems** are now over two nodes: `state_machine_safety` is a plain
wand on two `own_raft_ghost`s (from `is_committed_agree`);
`leader_completeness` is a fancy update (`↑raftN ⊆ E`) that opens the
invariant for the table. `cluster_ghost` is gone. `own_log_ghost` and
`own_raft_ghost` are no longer `Timeless` (they hold an `inv`).
