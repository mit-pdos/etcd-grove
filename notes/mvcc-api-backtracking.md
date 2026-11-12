# mvcc's API: how much backtracking, and why (2026-11-04)

A read-only analysis of the mvcc API work: branch `worktree-mvcc-rand-tester` (rounds 1-13 and the
round-9 candidate proof, never merged; `origin/mvcc` is an older branch already in `lean`, with no
API work) and branch `mvcc-api` (36 commits on `origin/lean` at `5eea04e0d6`, through `648d8e2bf4`).
Sources: `git log --numstat`, `notes/mvcc-api-candidate.md`, `notes/mvcc-api-invariants.md`,
`notes/decisions.md` (the six mvcc API entries at the end), `notes/mvcc-api-clients/`, the
scratch reviews in `~/mvcc-api-candidates/`, and the session transcript (`c63db8ef…jsonl`,
from 2026-11-02 16:46). All times are UTC.

The goal, in the user's words (2026-11-03 07:33): "we don't want to write a bunch of proof, later
realize we need a stronger spec, and then redo all the proof again". The user had set the order
before that (2026-11-02 16:46): specs, frozen; then invariants, informally, frozen; then the proof.

## Summary

| Phase | Written then discarded or reversed | Caught by |
|---|---|---|
| Rounds 1-9 and the round-9 candidate proof (11-01 19:15 to 11-02 14:15, before the spec-first order) | **~6,840 Lean lines**: 1,272 of spec (rounds 1-9) and 5,564 of proof and spec (P1-P5: 5,179 `Proof/`, 385 `Spec/`). None of it is in `HEAD`. | The user's request at 16:46 for the smallest API complete for etcd; the stale base (866 commits behind `lean`, before M2) |
| Freeze 1 (06:12) to freeze 2 (17:29) | 3 rounds (14-16), 12 commits to `Api.lean`/`ApiState.lean`, +283/−111 lines. One opaque predicate added (`wsSentLb`), one pure definition replaced by an opaque one (`imageOf` → `mvccImage`), 6 laws and 2 definitions added. No proof existed yet. | Client assessments and drafts (7 items), reviewers (5), the user (3) |
| Invariants freeze (06:35) | 4 sections superseded within 11 hours (§4.3 three times; §1's stream ghost; §1's carry-through, twice) | Round 15/16, the stage-1 proof agent |
| After freeze 2 | 1 statement change (`mvccImage_snapshot.law`'s `σ.crev = -1` dropped, a strengthening, known before the freeze) plus additive theorems. Forced rework: +168/−65 in the backend and server proofs to strengthen the `Snapshot` axiom | Review of round 16 (F1), decided by the user |
| Stage-1 strategy | `Api/InvStoreX.lean` (810) and `InvWatchX.lean` (276), **1,086 lines**, built 18:10-18:15 and deleted at 03:38 (`671a476f7a`). About 385 lines reappear reworked (`InvStore` +188, `Api/Instance.lean` 161, `Api/Ghost.lean` +36). Net loss is about 700 lines, and the watch half (276) still has to be redone in place | The stage-1 agent itself, 15 minutes after building them |
| Accidents | `shapes.law` deleted with a neighbouring edit and restored 4 minutes later (`d43039ac79` → `987188c9ec`). **`notes/status-history.md` truncated from 19,202 to 2 lines in `648d8e2bf4`** (pushed; still broken at `HEAD`) | The txn drafter; this analysis |

**The verdict.** Spec-first worked where it was fully applied. Since the spec-first order took
over, discarded proof has fallen from about 5,200 lines to about 700. The second freeze has held
for 11 hours, with one anticipated strengthening that no client depends on. Every post-freeze-1
change was found before any proof used the API. The backtracking that remains has three causes:

- The first freeze skipped the repository's own Freeze criteria: callers' glue and a Probe.
- The invariants were frozen informally, without typechecking or sizing them.
- One reversal came from the coordinator's own instruction. It contradicted the user's M1 decision
  and the frozen invariants note.

## 1. Spec-level backtracking

### Freezes and rounds

| Event | Time | Rounds since the previous event |
|---|---|---|
| Rounds 1-9 in-repo (`8bd75f7cc2` … `262b256730`) | 11-01 19:15 to 11-02 07:34 | 9 (4 after `spec-reviewer` reviews, 1 after a user critique, 1 applying the user's decisions) |
| Round-9 candidate proved (P1-P5) | 11-02 09:42 to 14:15 | (no freeze) |
| Rounds 10-13, scratch files `~/mvcc-api-candidates/MvccApiR1{1,2,3}.lean` (654, 806, 891 lines) | 11-02 16:46 to 11-03 04:10 | 4, plus 3 rounds of user answers and decisions 1-3 |
| **Freeze 1** (`aecfa65151`, 826 + 194 lines) | 11-03 06:12 | |
| Invariants frozen (`4a5cbd6a28`, round 3) | 06:35 | 3 rounds of the invariants note |
| **Reopened** (the user's "every spec and invariant first", `5ca666ee81`) | 07:33 | **1 h 21 min after freeze 1** |
| Rounds 14, 15, 16 | 07:45 to 17:24 | 3 |
| **Freeze 2** (`679fa3fc5e`, with three client drafts, 1,992 Lean lines) | 17:29 | |
| F1 premise dropped (`648d8e2bf4`) | 11-04 04:14 | 0 rounds; 1 change |

### Every statement change after freeze 1

| Commit | Change | Found by | Could an earlier step have caught it? |
|---|---|---|---|
| `d3a8e46433` (round 14, A1) | `wsSentLb ι n`, a new opaque predicate, given by `Watch` at the stamp | Watch assessment (G1): sendLoop's drain before a `Created` response | **Yes.** The repository's Freeze step requires "every caller's glue written" (`notes/spec-first-plan.md`, "The phases"). Freeze 1 had no client glue; `serverWatchStream__sendLoop.lean:1464` uses the fact today |
| `d3a8e46433`, `d43039ac79` (A2) | The non-blocking receive law, merged with the blocking one into one channel law | Watch assessment (G2); reviewer r14 (merge) | Yes, the same reason |
| `d3a8e46433` (A3) | A compaction response's revision is `0` | Watch assessment (G3): client/v3 relies on it | Yes, the same reason |
| `d3a8e46433` → `d43039ac79` → **deleted** in `e262e30763` | `mvccTxn_small`, a state-level size law. The first draft was false (reviewer r14: `keySized` holds of a read-locked view only). It was repaired in 10 minutes, then deleted by round 15 | Txn assessment (T1); reviewer r14; **the user**: "Why would the client need a size bound from sigma?" (16:04) | Yes: the need was the sort's premise on a range's results, `txn/range.go:125`. The principles "a fact the caller needs of a result belongs at the call that returns it" and "do not overspecialize" were added only after it (`dbc5f67e02`, `8f1ef62790`) |
| `d3a8e46433` (A5) | The lease bucket's delete law gives back `End`'s triple | Server assessment; reviewer r14 | Yes (client glue) |
| `d43039ac79` | `wsSentLb_zero.law`, for a refused create's drain | Reviewer r14 | Yes (client glue) |
| `d43039ac79` → `987188c9ec` | `shapes.law` deleted by accident, then restored | Txn drafter, 4 min later | Not a design change: an edit replaced a block that held two laws |
| `3bb20b69b3` | The range deleter is not `nil` (S2); names inhabited (`names_nonempty.law`, S3) | Server drafter | Yes (client glue) |
| `e262e30763`, `8f1ef62790`, `b01d7bada3` (round 15) | `stateOk`/`kvSortOk` at the `Range` contracts; `Restore` takes `⧖ (logCh σ'.log)` | The user's (D) | Partly. The `Restore` receipt was reviewer W3's option on 06:13 (`review-invariants.md`), not taken *because the spec was frozen* (§3 below) |
| `2f43a03a89` (round 16) | `mvccImage` (opaque, with its receipt) in place of the pure `imageOf`; `Restore` takes no receipt; positivity at the results | The cross-review §1 (`xreview-clients.md`): round 15's premise was circular, since the server's certificate got the receipt from the sender's mvcc internals (`SnapSendBranch.lean:784`); also the user's "hide the receipt in an existing abstract predicate" (16:29) | **Yes.** W3 had traced the receipt one step, to `etcdserver/InvImage.lean:148`. One more step, to its producer, shows the internals that the API hides |
| `d810bc697a` | The history's receipt at each step that changes it; `Restore`'s length premise dropped | Cross-review §1: client/v3's exported `kvLogOk` needs `LogSmall` | Yes, if the assessments had covered client/v3's exported results (cross-review §5: "client/v3's KV path is covered by no draft") |
| `ac1e686407` | `mvccImage_snapshot.law` (the sender), `reach_logWf.law`, the lease delete's receipt | Server draft (G3, the snapshot path is linked: `Link.lean:2407`) | Yes: the snapshot path was in rounds 12-13's backend survey; the sender side was not |
| `6cc29c14f0` | F1: `σ.crev = -1` on `mvccImage_snapshot.law`; F2: `isMvcc` in its pre; F3: `mvccImage_fresh.law` under `|==>` | Reviewer r16 | **Yes.** The law was added 30 minutes earlier (`ac1e686407`) as a consequence of `backend.Snapshot.spec` without checking the axiom's postcondition. The axiom says nothing of the compaction keys after a write since the open |
| `648d8e2bf4` (after freeze 2) | `σ.crev = -1` dropped; the axiom strengthened in place (`fkdOwn`, `γ.fkd`) | The user ("Strengthen the axiom", 11-04 02:47) | Known at freeze 2: frozen with a marked temporary premise. It cost 168 added and 65 deleted lines of backend and server proof, plus an `axiom` re-attack (in progress) |

**Who found them** (after freeze 1, by item): client assessments and drafters 7 (G1-G3, T1, A5,
S2/S3, the sender's image), the cross-review 2 (the circular receipt, `kvLogOk`), `spec-reviewer` 5
(A4 false, merge, `wsSentLb_zero`, F1, F2/F3), the user 3 ((D), hide the receipt, strengthen the
axiom). The round-14 → round-15 size law was found by the user's question, not by any reviewer.
Reviewers found it *false*, not *unneeded*.

**After freeze 2**: no surprise. The only change was decided before the freeze. Additive
vocabulary lemmas (`83a7d72ed5`: `reach_logWf` proved, `logCh_*`, `pendItems_nil`) are review F7,
planned at the freeze.

## 2. Proof- and module-level backtracking

### The round-9 candidate proof (`worktree-mvcc-rand-tester`, never merged)

- **What.** P1-P5 of `notes/mvcc-api-proof-plan.md`: an "abstract mode" of the store's ghost state
  (`cad9d508e3`), `specA` variants of today's specs, and `specC` candidates proved for about 30
  functions and the first laws (`ApiImpl`, `ApiLaws`, `ApiLemmas`, `ApiWatchImpl`, `ApiWatchLaws`,
  `RdCode`; `watchableStoreTxnWrite__End` +544, `watchStream__Watch` +420, `InvStore` +321, …).
- **Size.** `git diff cb10f4ec56 e59d153a1a`: +5,179/−92 in `Proof/` and +385/−278 in `Spec/`, over
  4.5 hours. With rounds 1-9's +1,272 lines of spec that is about **6,840 lines, none of which
  survives at `HEAD`**. No `specA` or `specC` remains, and the six `Api*` and `RdCode` modules are
  gone. The design ideas were carried over: the two-step commit, the read's update, and the
  watcher's stamp.
- **Why discarded.** The candidate was proved against no client. Its own end-state note
  (`9635dcfe58`, 16:32) found the server could not move onto it: no `Watch` at revision 0, no
  filters, no compaction, no `Restore`, no hashes, no lease. It also had 17 opaque predicates where
  rounds 10-11 found 8 sufficient. And it was built on internals 866 commits behind `lean`, from
  before M2's compaction over the real backend. This loss came *before* the spec-first order, and
  it is what the order was set up to prevent.

### The parallel internals (`mvcc-api`, retired)

- `Api/InvStoreX.lean` (810 lines, `baed93cba6`, 18:10) and `Api/InvWatchX.lean` (276 lines,
  `cc74c18040`, 18:15) were built with no `sorry`. They were found too narrow at about 18:27 and
  deleted in `671a476f7a` (11-04 03:38). Between those times the usage limit paused work for 7 h
  10 min (19:02 to 02:12). The decision that created them (`0d75dde9f0`, 17:55) was superseded
  **32 minutes later**.
- **Reused.** The slot shapes, the freeze/thaw device and the per-proof ghost updates in the
  hand-off (`notes/mvcc-api-invariants.md`, "Hand-off: the parallel internals' invariants") moved
  into `InvStore` (+188/−39), `Api/Instance.lean` (161) and `Api/Ghost.lean` (+36). That is about
  385 of the 1,086 lines.
- **Lost.** About 700 lines. The watch half (`watchStoreInvX`, `watchStreamInvX`, `streamAbs`,
  `isWatchableStoreA`, the stream's countable ghost names) is retired but **not yet redone in
  place**. It is "Left, 1" of the slots hand-off.
- **Kept.** `Api/Ghost.lean` (179 → 216 lines) and `ApiGhost.lean` (98, the saved filters).

### Other rework

- `671a476f7a` changed 10 lock-opening proofs by small amounts. Its +463/−1,177 in `Proof/` is
  mostly the 1,086 retired lines.
- `648d8e2bf4`: the backend's batch invariant, `NewAlloc`, `UnsafePut`'s callers and
  `SnapSendBranch` carry the new `γ.fkd` (+168/−65). This is rework of reviewed trust-boundary
  machinery (`notes/axiom-review/backend-snapshot-fk.md` covered the earlier axiom), and the new
  axiom still needs its `axiom` attack.
- **`648d8e2bf4` truncated `notes/status-history.md`** (−19,201 lines, 2 left: the entry that was
  meant to be appended). This breaks the file's append-only rule and loses data on a pushed
  branch. Restore it from `648d8e2bf4~1:notes/status-history.md` with the new entry appended.
- Scratch candidates R11 → R12 → R13 (2,351 lines in all) superseded one another. That is
  ordinary design iteration, not rework of proof.

## 3. Strategy reversals

| Decision | Made | Superseded | Interval | What arrived late | Knowable up front? |
|---|---|---|---|---|---|
| Relative revision budget re-based at `Restore` (invariants §4.3), "the frozen spec does not change" | 06:35 | Round 15: receipt premise on `Restore` (16:13); round 16: `mvccImage` (16:34) | 9.6 h, then 21 min | That the client needs the receipt anyway (`kvLogOk`), and where the server gets it | **Yes.** W3 offered the receipt premise at 06:13. The relative budget was chosen only to keep the 6-hour-old freeze, then reversed. Three designs of one fact in 10 hours |
| `ι.sst`/`ι.reg` hold `StreamState`/`WInfo` (§1) | 06:35 | Stage 1, `f7f73d485c` (17:54): filters are functions, and ghost values must be countable | 11.3 h | Perennial's `ghostVar` needs `Countable` | **Yes**, by declaring the ghost names' types in Lean. The invariants were frozen informally |
| M2 (today's specs as corollaries; the coordinator's recommendation) vs **M1** (all at once, build red until clients move) | User chose M1 at 07:28 | (never formally; see next row) | | | |
| Stage-1 prompt: "Existing proofs must keep proving their current statements" | 17:29 | Blocked at 17:55 | 26 min | The prompt contradicted the user's M1 and the coordinator's own analysis at 07:06 ("once the new ghost state exists, today's specs can no longer be proved as they stand") | **Yes**: it was in the transcript and in the M1 entry |
| (c) parallel modules for the five proofs whose statements change; today's untouched | 17:55 (`0d75dde9f0`) | 18:27: slots in place (decision entry `671a476f7a`) | **32 min** | A lock's invariant is fixed at creation, so every proof that opens `s.revMu`, the writer's invariant, `s.mu` or `ws.mu` (about 25 proofs) is redone over the copies | **Yes.** The frozen invariants note §4.2 (`4a5cbd6a28`, line 118) already listed the openers: "carried through every proof that opens and closes those (`storeTxnWrite.End`, `store.Read`, `updateCompactRev`, `watch`, `syncWatchers`, `moveVictims`, `RestoreMoves`, `NewStore`, the fractional instances)". `671a476f7a` changed that set plus `store.Restore`. A grep of `revMuInv_open`/`writerInv_checkout`/`watchStoreInv` users would have sized it in minutes |
| `mvccImage_snapshot.law` for a never-compacted store | 17:24 | The user: strengthen the axiom (02:47) | 9.4 h wall (7 h paused) | The user's choice of a trust-base change | It was the user's decision, raised before the freeze: not a reversal by surprise |

**A pending risk.** The slots-in-place design keys a slot on `StoreNames.api : Option
api.AbsNames`, and `isStore` asserts `api = none`. It works like a mode, which the frozen invariants
note excludes ("in every store, no mode", §1) and which the user rejected as M3 at 07:28 ("the kind
of split you said you don't want"). Its proofs do not split, because the slot steps are generic,
so it may well satisfy the user's real concern (no near-duplicate proofs). But the coordinator
decided it, and the user was not shown it next to M3. If the user objects, every lock-opening
proof is edited a third time. Ask now, before stage 1 continues.

## 4. Root causes

1. **Freeze 1 skipped the Freeze criteria.** The repository's plan (`notes/spec-first-plan.md`)
   requires every caller's glue before the Freeze, and a Probe (an easy and a hard proof) before it.
   Freeze 1 was declared on reviewer soundness alone, "nothing unsound or incomplete", where
   incomplete was judged by reviewers reading the clients, not by drafting their specs. It reopened
   after 81 minutes, and 7 of the post-freeze items came from client drafts. Freeze 2, made after
   the drafts, has held. No Probe was ever run, and a Probe through one lock-opening proof would
   have found the lock-invariant scope (row 5 of §3) and the countability problem (row 2).
2. **Reviews checked laws against the Go code, not against the statements available to prove
   them.** F1 (a new law over `backend.Snapshot`'s axiom, written without reading the axiom's post)
   and the circular receipt (a premise traced to the server's certificate but not to its producer,
   which the API hides) are the same failure. "Every premise has a source the client sees" is in
   PRINCIPLES.md, but nothing makes a reviewer follow a source *in the post-migration world*, or
   check a law against the *trusted statement*.
3. **"Frozen" was used as a reason to prefer a worse design.** The invariants round chose the
   relative budget over W3's one-premise fix to keep a 23-minute-old freeze. The stage-1 prompt's
   "keep today's statements" kept a green build that the user had already traded away for M1.
   Both constraints were self-imposed, and both were reversed within hours. The user's rule
   (memory: "frozen specs, no silent changes") is about *weakening* reviewed specs without asking.
   It does not mean a frozen statement outranks a simpler design found within the design phase.
4. **Scope estimated from memory, not from the notes or code.** (c) planned five proofs, but §4.2
   listed eight, plus the fractional instances. The lock-invariant fact (an Iris invariant's body is fixed at allocation) is
   general knowledge, so the narrower scope was an estimate nobody checked.
5. **Informal invariants.** Freezing the invariants in prose let a non-countable ghost type through.
   One `ghostVar` declaration would have caught it.
6. **Overspecializing to the first client found.** `mvccTxn_small` encoded txn's indirect need as a
   state law. The reviewers judged it for truth, not need, and only the user's question removed it.
   The principle now exists (`8f1ef62790`).
7. **Proof before scope (round 9).** Proof started on a candidate never checked against etcd's
   callers, on a stale base. That is the original 5,000-line loss, and the spec-first order fixed it.
8. **Edit hygiene.** A whole-file write of an append-only note (`status-history.md`), and a block
   replacement that took a neighbouring law (`shapes.law`).

## 5. Recommendations

### Candidate additions to `.claude/skills/spec/PRINCIPLES.md`

- **A law over a trusted spec is checked against the trusted statement, not the code.** For each
  law or contract whose proof must go through an axiom or a trust-boundary spec, the reviewer
  writes the derivation's outline from the axiom's text: which conjunct of its post gives which
  fact. (mvcc round 16, F1: `mvccImage_snapshot.law` was true of the Go code and unprovable from
  `backend.Snapshot`'s axiom.)
- **A premise's source is traced to its producer under the new API.** Each premise that a client
  supplies is followed back, past the client's certificate, to what first makes it. If that is an
  internal of the library the API hides, the source is circular. (Round 15's `⧖ (logCh σ'.log)` on
  `Restore`, from the sender's `idxCert`.)
- **Reviewers ask "is it needed?" as well as "is it true?"** For each new law, name the client
  step that consumes it. If a consumer needs a fact of one call's result, the fact goes at that
  call. (Round 14's `mvccTxn_small`.)
- **A freeze is no reason to prefer a worse internal design while the design phase is still open.**
  If an internal workaround exists only to keep a frozen statement, raise the statement change
  (with both designs side by side), not the workaround. (Invariants §4.3: relative budget, reversed
  twice in 10 hours.)

### Candidate additions to the process (`notes/spec-first-plan.md`, the Freeze and Probe steps)

- **Freeze gate, unchanged but enforced.** No freeze without every client's glue drafted and
  typechecked over the API. Freeze 2 met this; freeze 1 did not. Record in the freeze's decision
  entry which drafts and which reviews it rests on.
- **Invariant freeze in Lean, not prose.** Before an invariants note freezes: (a) the ghost names'
  types declared (a `Ghost.lean` that builds); (b) each opaque predicate's definition written as
  a `def`, with its laws `sorry`; (c) a committed list, *made by grep*, of every proof that opens
  each invariant whose body changes, with counts. This list is the stage's scope.
- **A Probe before fan-out.** Prove one hard step end to end at the API instance (for example
  `storeTxnWrite.End`'s bump, which opens `s.revMu` and the writer's invariant and fires the
  client's update) before writing the hand-off for parallel agents.
- **Stage prompts quote the decisions.** A constraint in a stage prompt (such as "today's
  statements unchanged" or "green build") must cite the decision entry it comes from. If no entry
  supports it, or one contradicts it (M1), the coordinator resolves that before launching the
  agent.
- **Strategy choices get a sized comparison and a "rejected-option" check.** Before choosing how
  to organize a proof stage, write down for each option the files it touches (from the grep above).
  Check it against the options the user already rejected (M2, M3). An option that resembles a
  rejected one goes to the user.
- **Measure.** Add the mvcc API's freezes (`aecfa65151`, `679fa3fc5e`) and the invariants freeze
  (`4a5cbd6a28`) to `etc/spec-churn.py`'s `STAGES`, so the churn is measured mechanically from
  now on.
- **Append-only files are edited by appending** (`cat >>` or an Edit at the end), never by Write.
  A pre-commit check could refuse a diff that deletes more than N lines of `notes/status-history.md`.

### For the remaining stages

- **Now.** Restore `notes/status-history.md`. Show the user the slots design next to M3 and M1 (the
  pending risk in §3), and get a decision before more proofs carry the slot.
- **Stage 1's rest.** Do the watch half in place by the same pattern (`watchStoreInv`'s and
  `watchStreamInv`'s slots, `ι.rcv`). First list, by grep, every proof that opens `s.mu` (watchable)
  and `ws.mu`. Then do `isStoreA`, `isWatchableStoreA` and `isWatchStreamA`, and declare `ApiImpl`'s
  definitions with the laws `sorry`. At that point every opaque predicate has a definition that
  typechecks.
- **Before stage 2's fan-out.** Run one Probe proof per kind: a two-step commit (the watchable
  `End`), `wsRecv_ok.law` (claimed to be a pure entailment), and `mvccImage_snapshot.law` over the
  strengthened axiom, after the `axiom` attack reports. A failure there reopens the API with no
  other proof written.
- **Before M1.** The client drafts are frozen (`notes/mvcc-api-clients/`). Before the migration,
  cross-check them against the *defined* predicates (not the opaque ones) once `ApiImpl` exists.
  Probe the hardest client step: v3rpc's sendLoop drain with `wsSentLb` and the non-blocking
  receive law.
