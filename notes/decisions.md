# Decisions

Why the development is the way it is. Newest last.

Record a decision when you pick a specification, an invariant, an abstraction
boundary, or a trust boundary, **and there was a real alternative** — the point
is to stop the next agent from silently re-deciding it the other way. Say what
was rejected and the cost that killed it; that is the part that saves time. Skip
routine choices with an obvious answer.

To revisit one, add a new entry and put a "Superseded by …" line on the old one
rather than editing it.

---

## Keep upstream Go module and Rocq logical paths

**2026-09-11 · accepted**

`etcd-grove` is a fork of `mit-pdos/perennial`. When setting the fork up, the
obvious sweep is to rename every `mit-pdos/perennial` reference to
`upamanyus/etcd-grove`. Two of those references are not URLs but identifiers
the build depends on:

- the Go module path `github.com/mit-pdos/perennial` in `go.mod`, which Goose
  embeds in its output, so it appears in ~71 files and names three generated
  directory trees (`new/code/github_com/mit_pdos/perennial/...`, likewise under
  `new/generatedproof/`, and `goose/testdata/**/*.gold.v`);
- the Rocq logical paths `Perennial` and `New` in `_RocqProject` and
  `perennial.opam`, which every `From Perennial Require` / `From New Require`
  in the repo depends on.

**Decision:** leave both alone. Rebrand only things that identify *the
repository* — README and its CI badge, `perennial.opam` metadata,
`CONTRIBUTING.md`, `docs/`, the flake description, the GitHub workflows.

**Rejected — rename the Go module to `github.com/upamanyus/etcd-grove`.**
Cost/benefit. The benefit is zero for the etcd work: the etcd Go code lives in
separate repos and translates to `go_etcd_io/...` paths, so this module path
only ever names Goose's own test fixtures. The cost is real and recurring —
every future `git merge upstream/master` would conflict across all of
`goose/*.go` and every `.gold.v`, since Goose is actively developed upstream.

**Rejected — rename the Rocq logical path `Perennial` → `EtcdGrove`.** Rewrites
the import line of essentially every `.v` file, guarantees a conflict on every
upstream merge, buys nothing. The framework genuinely is Perennial.

**Rejected — rename `perennial.opam` to `etcd-grove.opam`.** `flake.nix`
derives its package name from that filename via opam-nix, and
`etc/install.sh`, the Makefile, CI and the docs all name it. The package still
installs logpaths `Perennial` and `New`, so the name is not wrong.

**Consequences:** upstream merges stay mechanical — `git fetch upstream && git
merge upstream/master` touches only files we actually edited. Anyone reading
`go.mod` or an import line sees `mit-pdos/perennial` and may think the fork is
misconfigured; `README.md` says why, and so does this entry. If the fork ever
diverges enough that upstream merges stop happening, this is cheap to revisit:
a scripted `sed`, three `git mv`s, and a Goose regeneration.

---

## Keep the notes plaintext; no hooks or scripts

**2026-09-11 · accepted**

The notes system was first built with `topics/`, `decisions/` and `journal/`
subdirectories, a README and template in each, two Python hook scripts
(`etc/agent-notes/session-start.py` injecting `STATUS.md` into each session,
`etc/agent-notes/stop-check.py` nudging when `.v` files changed but `notes/`
did not), a `.claude/settings.json` wiring them up, and a Claude-Code-specific
`/notes` skill.

**Decision:** delete all of it. Seven flat markdown files in `notes/`, and
plain instructions in `AGENTS.md`. The general principle, from Upamanyu: **only
add structure where there is a demonstrated benefit.**

**Why the hooks lost.** Two independent reasons. They are Claude-Code-specific,
and this project will see other coding agents, so behaviour encoded in
`.claude/settings.json` silently does not happen under a different tool —
whereas a sentence in `AGENTS.md` or `notes/README.md` is read by all of them.
And they were speculative: nobody had yet skipped writing notes, so a `Stop`
hook was solving a problem that had not been observed, at the cost of two
scripts to maintain and a blocking interaction to get wrong.

Same reasoning killed the subdirectory scaffolding: `topics/README.md`,
`decisions/README.md` and `journal/README.md` were index and template files
with no content, and indexes that have to be hand-maintained go stale.

**Consequences:** nothing guarantees the notes get updated — it rests on
`AGENTS.md` and habit. That is the accepted trade. Revisit only with evidence:
if notes are demonstrably being skipped, automate *that one step*. Likewise
split a file into a directory when the file is actually unwieldy, not in
anticipation.

---


**2026-09-13 · accepted**

Reviewing what the raft proof *assumes* meant reading 2429 lines of Rocq across
six files and filtering out the proofs by eye. The trust base is currently 46
`Axiom`s and 17 `Admitted.`s in four files, and nothing listed them in one
place. `notes/STATUS.md` already carried two roadmap items about discharging or
justifying those axioms, and `raft-proof-map.md:77-79` already said "anything
not proved should be either discharged or explicitly justified here" — so the
need was recorded before the tool was; this is not speculative structure.

file down to the top-level theorem statements, the transitive closure of the
definitions those statements mention, and every axiom and admitted hole —
hiding proof bodies and proved helper lemmas. Plain text to stdout, so it
composes: `diff` of two revisions' output answers "did this commit widen the
trust base?" It did, immediately — running it across `HEAD~2..HEAD` showed
`election.v` going from 24 axioms to 22.

**Scope choice.** The alternative reading of "hide the proofs" is to show every
statement and fold only the `Proof.`…`Qed.` bodies. Rejected: a *proved*
helper lemma's statement is not something you have to believe, so showing it is
noise. The closure is seeded from roots **and** from every hole, since an
admitted lemma is itself trusted and the definitions in its statement are too.

**Rejected alternatives.**

- `coqdoc -g` already hides proof bodies, but has no notion of roots or
  reachability, so it cannot drop a proved helper — which is the whole point.
  Nothing in the repo invokes coqdoc, and there is no `rocq` binary in the
  container this was written in.
- `.glob`-based reachability was the tempting one: free output of every `make`,
  byte-offset addressed, with fully-qualified references *and* typeclass kinds,
  which would fix both approximations listed below. Killed by availability —
  `.glob` is gitignored, is not produced by `vos`/`vok`, and exists only for
  files built to `.vo`. At the time of writing only `election.v` and
  `election_proof/protocol.v` had one; `base.v`, `protocol.v`, `readonly.v` and
  `v3.v` did not. A trust tool that works on a third of the trust base is not
  a trust tool. Worth revisiting if the build ever guarantees `.vo`.
- `Print Assumptions` is the only ground truth and would catch assumptions
  inherited from Perennial/Iris that a textual scan cannot. Same availability
  problem, plus it cannot tell a deliberate `Admitted. (* Trusted *)`
  (`readonly.v:469,478`) from an unfinished one. Left as a follow-on.
- Editor folding via `etc/mixcode/mixcode.el` is Emacs-only, which the
  agent-neutral rule above rules out.

--self-check`, and the lossless round-trip is asserted on *every* run. The
evidence against a test file is in this repo: `etc/test_coqc.py` is run by
nothing and has rotted to the point of being unimportable — it does `from coqc
import ...` and the module was renamed `rocqc.py`. A test nobody runs reads as
coverage it does not provide.

**Consequences — what it does not tell you.** It reads text, not Rocq, so it
reports the trust boundary *as written in the files you give it*: it cannot see
axioms inherited from Perennial, Iris, or the Goose translator, nor
`new/trusted_code/` and `new/golang/defn/`, all of which are really in the TCB.
Reachability is by identifier name, so it over-approximates under shadowing,
and typeclass resolution is invisible to it — every `Instance` and `Notation`
is therefore shown wholesale rather than resolved. Over-approximating shows you
more than you must trust, never less, which is the safe direction. It also
refuses to run on a tree where `etc/disable-qed.sh` has rewritten `Qed.` to
`Admitted.`, which would otherwise report every proof in the file as a hole.

---

## One file per function, via Rocq's module system

**2026-09-14 · accepted**

`election.v` was a single 1072-line `Section proof` holding 15 axiomatized
Hoare triples, 14 proved-or-admitted ones, 8 ownership predicates and 5 model
lemmas. Nothing stopped a second spec for the same Go function being written
elsewhere, and the only thing distinguishing a trusted assumption from a
finished proof was which `Section` a declaration happened to sit in. That is
not hypothetical: `raft_names` is declared twice (`protocol.v:30` vs
`readonly.v:51`), `is_quorum` twice (`election_proof/protocol.v:84` vs
`readonly.v:114`), and `readonly.v` axiomatizes `own_raft` as a second,
incompatible ownership story for the struct `own_raft_phys` already covers.

**Decision:** four files per Go function, under `election_proof/`, modeled
on `mit-pdos/xv6iris`:

| file | holds |
| --- | --- |
| `spec_<fn>.v` | `wp_<fn>_body` + `Module Type <FN>` with **one** `Parameter` |
| `postulates_<fn>.v` | `Module Type <FN>_POSTULATES`, `Include`ing direct callees |
| `proof_<fn>.v` | `Module <Fn>Proof (P : <FN>_POSTULATES) : <FN>.` |
| `link_<fn>.v` | the instantiation |

**What actually enforces the property.** Not the functor — opaque ascription
(`: <FN>`) is what stops anything bypassing the spec, and `Include` is what
makes a duplicate a *build error*: two signatures declaring the same label
give `Error: The label wp_raft__poll is already declared.` This was
demonstrated deliberately and reverted; do it again if you doubt it.

**Rejected — drop the functor, import callee modules directly.** Same
single-spec guarantee, and a stable link-file name gives the same edit
locality. What the functor buys in *this* repo is build shape:
`proof_becomeLeader.v` compiles against `reset`'s ~20-line signature rather
than its proof. One function re-checks in about a minute where the monolithic
`election.v` took upwards of twelve.

**Rejected — put the trust-boundary `wp_*` axioms behind Module Types too.**
They are `Prop`s so it would typecheck, but nothing about them will ever be
proved, so it buys ~20 extra signatures for nothing. They stay plain `Axiom`s
in `inv_*.v`. **Superseded by the 2026-09-18 entry below**, which reversed
this: the signatures buy enforcement, not proving, and an axiom is the last
claim that should sit outside the mechanism.

**Forced, not chosen — predicates stay out of the module system.**
`own_raft_phys` mentions `own_tracker`/`own_raftLog`/`own_raft_misc`/
`is_Logger`, and every `wp_*_body` mentions `own_raft_phys`, so a spec's
statement must elaborate before any module exists. Independently: a
`Definition` inside an ascribed module is opaque outside it (`iNamed` and
`rewrite /own_raft_phys` stop working), and an `Instance` declared inside one
never reaches the global instance table. With `:` everywhere, if a predicate
ever did become a Module Type field the two copies would fail to unify at the
first `iFrame` and name both offenders — so the invariant **"Module Types
contain only `Prop`-valued specs"** is compiler-enforced, not a convention.

**The `_body` carries its own binders**, so the `Parameter` is a bare
reference and the binder list exists once. Writing them with `` `{...} ``
generalization compiles but emits five "Ignoring implicit binder declaration"
warnings per file, and `` `(...) `` still emits one; naming all nine outright
is warning-free. The cost is that implicits are not inferred through a folded
`_body`, so each spec declares
`Arguments wp_<fn> {_ _ _ _ _ _ _ _}.` inside its `Module Type` — the short
prefix form, which leaves each function's own binders explicit.

**Corrected 2026-09-15.** This entry first said the `Arguments` had to live in
the `link_*.v` file because one inside the `Module Type` "does not survive
functor application". That was false — a `grep` artifact, the printed
`Arguments` line wraps — and the declaration belongs in the signature, where
every implementing module inherits it. Proofs likewise open with
`intros_ambient` (`election/defs.v`) rather than a positional `intros`; see
[gotchas.md](gotchas.md) for both, written up once.

**Consequences.** 51 files where there was one. `election.v` is an
aggregator that `Require Export`s every `link_*.v`; that is load-bearing,
because `make ci` builds only what `new/should_build.v` reaches, so a link
file nothing re-exported would silently go unchecked. The trust base is
unchanged — 49 axioms, 14 `Admitted` — and is now split structurally: an
`Axiom` in `inv_*.v` means *out of scope*, an `Admitted` in `proof_*.v` means
*in scope but unfinished*. (**The `inv_*.v` half of that reading was
superseded on 2026-09-18**: every triple about a Go function now sits in a
collection, so the `Axiom`/`Admitted` distinction is read off the
`proof_*.v` file and the keyword, not off the file kind.)

**Superseded within the same day:** the first cut gave `Step` four spec files
(one per message type plus the dispatch). Upamanyu pointed out that this is
four Hoare triples for one Go function, i.e. exactly what the refactor exists
to prevent. The three per-message-type triples are proof structure and are now
internal lemmas inside `proof_raft__Step.v`, sealed by the ascription. **If a
function ever seems to want two specs, that is the signal to look harder, not
to add a second `Module Type`.**

**Amended 2026-09-17:** the three branch lemmas moved to their own files
(`proof_raft__Step_MsgHup.v`, `_MsgVote.v`, `_MsgVoteResp.v`) so that they
check in parallel — see the entry of that date below. They are still not
specs: no `Module Type`, no `Parameter`, and only `proof_raft__Step.v` may
`Require` them. **Amended again 2026-09-18:** those files live in
`proof_raft__Step_helpers/`, so the top-level directory is four files per Go
function and nothing else — see the 2026-09-18 entry on the layout.

---

## The outbox lives in `nstate.t`; certification follows from the ghost, not from `own_raft_phys`

**2026-09-15 · accepted**

`own_raft_phys` used to require both outgoing queues to contain only messages
`γ` certified (`is_phys_msg`). That put the `is_message` obligation on `send`,
and since only `own_raft_ghost_step` produces `is_message`, **every function
that could reach a `send` had to own `own_raft_ghost`** — `campaign`, `hup`,
`Step`, `stepCandidate`. The ghost update could never be higher than the
innermost sender.

Now `nstate.t` has an `outbox : list msg.t`, `step` has no `sent` output (a
step's sends are the growth of `s'.(nstate.outbox)`), `own_raft_phys` relates
that field to the two physical queues and has no `γ` at all, and certification
is read off the ghost state with a new axiom:

    own_raft_ghost γ id s -∗ [∗ list] m ∈ s.(nstate.outbox), is_message γ m

`own_raft_ghost` now appears in exactly one spec (`Step`) and
`own_raft_ghost_step` is applied in exactly one proof file.

### Rejected: pre-certified sends

Keep the certified-queue invariant, but have callers take the ghost step
*first* and pass the resulting `is_message` tickets down, the way `send`
already took them. Cheaper — no change to `own_raft_phys`, no new axiom — and
it does get `own_raft_ghost` out of `campaign`/`hup`/`stepCandidate`.

Killed by what it leaves behind: `own_raft_phys` still carries a `γ` and still
asserts a ghost fact, so "this spec is phys-only" stays a manner of speaking
rather than something you can check. It also cannot express
`wp_raft__appendEmptyEntry` honestly (below), because a `MsgAppResp` has no
`mtype_of` and so can never satisfy `is_phys_msg`.

### Rejected: index `own_raft_phys` by the outbox instead

`own_raft_phys r id s ms msAA`, with the outbox as extra arguments rather than
a field of `s`. Same effect on ghost placement, but it widens every spec in
the development — including the five that otherwise change only by dropping
`γ` — and it splits "the abstract state of this node" across two places.
Putting it in `nstate.t` also makes `step`'s `sent` output redundant, which
simplifies `step_trans` and collapses `own_raft_ghost_step_1_1`.

### What it cost

One new axiom (`own_raft_ghost_outbox`, 49 → 50), and `own_raft_phys` relates
the model's single outbox to the two queues up to **permutation**
(`s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA`) rather than equality, because
`send` routes responses to `msgsAfterAppend` and everything else to `msgs`, so
an append to one lands in the middle of the concatenation. The fallback — two
`nstate` fields mirroring the two queues, with plain equality — was not needed;
`proof_raft__send_vote.v` went through with three small `omap`/`++` helpers in
`defs.v`.

### The payoff that was not the goal

`wp_raft__appendEmptyEntry` was **false**: it owned only `own_raftLog l`, but
`appendEntry` queues a `MsgAppResp` into `r.msgsAfterAppend`. The old design
could not state it honestly at all, because `mtype_of MsgAppResp = None` makes
`is_phys_msg` unprovable for it. Abstracting messages with a *partial*
`abs_msg_opt` and folding the queues with `omap` makes out-of-scope message
types drop out, so the honest statement is both expressible and trivial. Do
not make `abs_msg_opt` total.

### The rule this establishes

**No function below `Step` touches ghost state.** A spec below `Step` says
only which state the struct now refines and how the outbox grew — never that
the transition is *legal*. Legality is `Step`'s single `own_raft_ghost_step`.
If you find yourself adding `own_raft_ghost` to an internal spec, that is the
signal that something is being certified in the wrong place.

## 2026-09-16 — what may be assumed: only the top-level election restriction

Superseding the reading established on 2026-09-14 ("an `Axiom` in an
`inv_*.v` file means out of scope").

**Decision.** The only thing the election development may assume outright is
the *top-level* restriction: that `raft.Step` need handle only
leader-election messages. Everything in **core raft** — the log, the progress
tracker, `Progress`, `bcastAppend`, `newReadOnly` — is in scope and has to be
constructed and proved. Things genuinely outside the raft protocol may still
be assumed, and these are the ones that qualify: `slices.Sort`, the `Logger`
interface, the tracing hooks, and the RNG behind
`resetRandomizedElectionTimeout`.

**Why.** "Election does not reason about the log" was doing two jobs: marking
what the *model* ignores (fine — the log really is invisible to the protocol
state, because `isUpToDate` can only make a node decline, and declining is
always legal) and excusing an axiom about what the *code* does (not fine —
that is where `wp_raft__appendEmptyEntry` was able to be false for a day, and
where `step_win` was able to be false for four). An axiom about raft's own
code is a claim about the artifact under verification, and this project exists
to check those claims.

**Consequence.** `inv_tracker.v` was converted: `own_inflights`,
`own_progress` and `own_tracker` are real `Definition`s, their eight method
axioms/13 admits to 44/24 — the same facts, relabelled from "assumed" to "in
scope, unfinished", which is the point. `inv_raftlog.v`, `inv_misc.v` and
`inv_raft_phys.v` still need it; see
[raft-election-refinement.md](raft-election-refinement.md) for what each one
costs and for the one real design question in the pile (what the log
abstraction should be, given that `raftLog.storage` is a client-supplied
interface and wants an `is_Storage` predicate rather than an axiom).

## 2026-09-16 — `step_win` sends *some* appends, not one per peer

**Decision.** `step_win` (and `vote_resp_result`, `step_record_then_win`,
`spec_stepCandidate_MsgVoteResp`) now say a new leader broadcasts an
arbitrary list of `App` messages from `id` at the current term —
`app_sends id term ms`, possibly empty — rather than exactly
`(λ to, msg.mk mtype.App id to term false) <$> peers` for
`peers ≡ₚ elements (cfg ∖ {[id]})`.

**Why.** The old version was **false of the code**. `bcastAppend` visits each
peer and calls `sendAppend` → `maybeSendAppend`, which emits a `MsgApp` only
when the log and that peer's `Progress` allow: it returns early if
`pr.IsPaused()`, falls back to `maybeSendSnapshot` (a `MsgSnap`, or nothing)
if `raftLog.term(prevIndex)` or `raftLog.entries(...)` fails, and returns
without sending if `len(ents) == 0 && !sendIfEmpty`. One-per-peer *does* hold
immediately after `reset`+`appendEntry` under our scope assumptions, but only
via facts about the log and `Progress.State` that are nowhere formalised — so
asserting it was assuming log replication, not election.

**What it costs: nothing.** Election safety comes from quorum intersection on
`votes`, and no rule reads an `App`'s payload. A receiver only ever consumes
an `App` through `step_higher_term`, which cares about its term and that a
leader sent it — both still pinned. So the weaker rule refines the code and
supports the same election-safety check.

**Do not strengthen it back** without first making `own_raftLog` and
`Progress.State` transparent enough to prove the broadcast exactly. The
symmetric mistake is recorded one entry up: this is the third time a
plausible-looking bookkeeping claim about raft's outgoing messages has turned
out to be untrue.

## 2026-09-16 — `step_lose` means "cannot win", not "a majority rejected"

**Decision.** `step_lose`'s premise changes from
`is_quorum cfg (rejected s.(nstate.votes))` to
`¬ is_quorum cfg (cfg ∖ rejected s.(nstate.votes))`, and
`wp_ProgressTracker__TallyVotes` / `wp_raft__poll` / `step_record_then_lose`
change to match.

**Why.** The old premise was **false of the code**. Go's
`MajorityConfig.VoteResult` (`new/code/go_etcd_io/raft/v3/quorum.v`) computes

    q = len(c)/2 + 1
    votedCnt >= q            -> VoteWon
    votedCnt + missing >= q  -> VotePending
    otherwise                -> VoteLost

so `VoteLost` means *the candidate cannot still win*, however the remaining
voters vote. It does **not** mean a majority rejected. Concretely: 4 voters,
2 reject, 2 have not voted. Then `votedCnt = 0`, `missing = 2`, `q = 3`, so
`0 + 2 < 3` and Go returns `VoteLost` — while the 2 rejections are not a
quorum, since `is_quorum` needs `4 < 2*2`.

The identity that makes the correct form obvious:

    votedCnt + missing = size cfg − size (rejected ∩ cfg) = size (cfg ∖ rejected)

so `VoteLost ⟺ ¬ is_quorum cfg (cfg ∖ rejected)` — *the voters who have not
rejected are not a quorum*. (The `VoteWon` side was already fine:
`floor(n/2) + 1 ≤ v` gives `n < 2v`.)

**Why weakening is safe.** `step_lose` moves a candidate to follower **at the
same term** and creates no leader, so election safety — which is what the
model exists to provide — is untouched. The new premise still records *why* a
candidate gives up, which is real information about the algorithm; dropping
the premise entirely was considered and rejected for that reason.

**What this cost.** `stepCandidate` was already `Qed`, and its `VoteLost` arm
consumed the false `TallyVotes` postcondition, so that proof was **not sound
as it stood** — it was discharged from an `Admitted` lemma that could not be
proved. This is the strongest argument yet for the rule recorded in
[proof-effort.md](proof-effort.md): an `Admitted` lemma is not a placeholder
for work, it is an unchecked claim, and a `Qed` above one inherits its
falsity. Discharge the leaves before trusting the root.

It is also the **sixth** false or unprovable statement found in two days,
after `wp_raft__appendEmptyEntry`, `step_win`, `spec_raft__campaign.v`, the
`r.step` comment in `inv_raft_phys.v`, and `own_progress`'s missing
`IsLearner`. Five of the six were claims about what raft's code does that
nobody had checked against the generated body.

## 2026-09-16 — a false `Admitted` gets repaired, even when it stays `Admitted`

`wp_ProgressTracker__Visit` turned out to be false: its precondition owned no
part of the tracker struct, while `Visit` has a pointer receiver and reads
`p.Progress` through it. It is also *unprovable* even once repaired, because
of a Goose defect (see `bugs/`). So there were three options:

1. leave it, note the falsity, and move on — it cannot be proved anyway;
2. repair the statement and fix the caller, knowing it stays `Admitted`;
3. delete it and inline the assumption at the call site.

**(2).** `reset` is `Qed` on top of it, and `becomeFollower`,
`becomeCandidate` and `becomeLeader` rest on `reset`. A `Qed` above a false
`Admitted` is unsound; a `Qed` above a *true* `Admitted` is sound modulo a
stated debt. Those are completely different situations, and the distinction
is worth the cost of the repair even when the repair does not make anything
provable today.

The repair has a shape worth knowing. `own_tracker` is indexed by the tracker
*value*, so that it is disjoint from `own_raft_phys`'s `r ↦ rv` by
construction — that decision stands and is right. The consequence is that
every **pointer-receiver** method on the tracker needs `trk ↦ tv` as well.
`Visit` additionally has to *lend* it to the closure rather than keep it:
`Visit` reads `p.Progress` on every iteration while the closure reads
`r.trk.MaxInflight`, different sub-fields of the same value at different
times. So `visit_closure` gained `trk` and `tv` parameters, and
`proof_raft__reset.v`'s caller invariant `I` now carries the
`raft_split_trk` continuation wand in place of `r ↦ rv`.

(3) was rejected because it hides the obligation where no audit will find it.

## 2026-09-16 — `bugs/` for tooling defects

A new top-level directory. The bar for a file in it: **a proof cannot be
completed, and no amount of proof-writing skill would change that.** One file
per defect, with the evidence, a probe that was actually run, the fix, and
what is blocked.

The alternative was another `notes/` file. Rejected: `notes/` is oriented
around *this* proof's state, and a reader scanning it for "what is left to
prove" should not have to sort our debts from Goose's. The split also makes
the right thing easy — when four `Admitted`s share one root cause, the
cause gets one file and the four get one-line pointers, instead of the
diagnosis being copied four times and going stale in three of them.

Deleted when fixed; git remembers.

## 2026-09-17 — the stepping tactics hide the program text from the proof mode

**accepted**

`proof_raft__Step.v` took ~45 min and 11.3 GB to check. Profiling one lemma
showed the time was not in the proof but in the tactic engine: `wp_pure`
spent ~40% stripping laters from the context (a typeclass search that unfolds
every hypothesis), and every failing proof-mode typeclass search against the
`WP` goal (`done`/`//`, `iPureIntro`, `iSplitR`, `iApply`'s bookkeeping) cost
seconds because unification is linear in the ~500KB program term.

Decision, in `new/golang/theory/proofmode.v`:

1. A pure step skips `MaybeIntoLaterNEnvs` when the context has no `▷`
   syntactically (`tac_wp_pure_wp_no_later`, `tac_wp_rec_no_later`).
2. `wp_bind_next` let-binds the evaluation context (`__wp_ctx := λ e, fill K
   e`) so that `wp_apply`'s `iApply`/`iPkgInit`/`as` run on a small goal;
   `wp_apply` unhides before returning.
3. `done` is redefined (`Ltac done ::=`) to let-bind the body of a `WP` goal
   before running stdpp's `done`; `solve` rolls it back.
4. `wp_hidden tac` and `wp_start_unfold` are offered for the user-level
   equivalents (`iNamed` mid-body; destructure before the body unfolds).

The invariant kept: **when a tactic returns, the program is visible in the
goal.** Hiding is internal to individual tactics.

Rejected:

- *Keep the body hidden at rest and unhide in the stepping tactics only.*
  Fastest for every IPM tactic, but `rewrite Hb` on the program text — the
  idiom these proofs use to resolve a `bool_decide` before `wp_auto` — would
  fail to find its occurrence, and reading a goal would mean reading a let-in.
- *`Typeclasses Opaque` on the abstract predicates* to stop the later search
  unfolding them. Breaks `iNamed "Hphys"`, which relies on typeclass
  unfolding of `own_raft_phys`.
- *Making the program term smaller* (primitive strings for variable names and
  literals). Right in principle, but it is a change to `goose_lang`'s `expr`
  and to Goose, far outside this repo's scope.
- *A faster `iFrame "∗#%"`.* That is Iris's `Frame` search; the fix is not to
  use it for a 25-conjunct re-seal (`own_raft_phys_intro`).

Cost of the decision: `done` is now a copy of stdpp's definition plus a
guard, so a future stdpp change to `done` has to be mirrored by hand — and
the copy has to be *verbatim*: the first version had an extra arm (`case H;
clear H; done` on `¬_` hypotheses, misremembered from a truncated grep) that
was exponential in the number of negated hypotheses and cost 345s on one
`//` in `proof_raft__campaign.v`. An A/B against the stashed old framework
is what caught it; the same-day per-command timings are in the 2026-09-17
journal entry. Also, a later hidden behind a definition is no longer
stripped by a pure step.

## 2026-09-17 — `Step`'s branch lemmas check in parallel, one file each

**accepted**

After the tactic-engine work `proof_raft__Step.v` still took 8.7 min at
`-vok`, and 5.4 of those were `wp_Step_MsgVote` (its `Qed` alone is 88 s).
The three branch lemmas are independent proofs of independent Go paths that
happen to share a body, and `make -j` already checks separate files in
parallel. So `proof_raft__Step_MsgHup.v`, `proof_raft__Step_MsgVote.v` and
`proof_raft__Step_MsgVoteResp.v` each hold one lemma inside a functor over
`STEP_POSTULATES`, and `proof_raft__Step.v` instantiates the three and proves
the one triple in `STEP` from them. `MsgVote` was then still the whole
critical path (6:00 of a 5:55 wall), and it is two independent term cases,
so it is split once more: `proof_raft__Step_MsgVote_gt.v` (`m.Term >
r.Term`) and `_le.v`, combined by a two-line case split in
`proof_raft__Step_MsgVote.v`. The sum of the parts is unchanged; the wall
clock is the longest part. Numbers in STATUS.md and the journal.

What this does *not* change: `Step` has one spec, `spec_raft__Step.v`, and
the branch lemmas have no `Module Type` and no `Parameter`. The earlier
decision's concern was four Hoare triples for one Go function *stated as
specs*; these are proof structure. What is weaker than before: the ascription
no longer hides the branch lemmas from other files — a file that `Require`s
a branch file and instantiates its functor can use its lemma. The rule is
therefore conventional: **only `proof_raft__Step.v` may `Require` a
`proof_raft__Step_*.v` file**, and the file header says so. (Since
2026-09-18 those files are in `proof_raft__Step_helpers/`, which makes the
convention visible in the directory listing as well as in the headers.)

Rejected: keeping one file and relying on Rocq's `-async-proofs` to overlap
the `Qed`s with tactic execution. Measured: 9:11 against 9:29, at 11.3 GB
instead of 6.0 — the workers copy the state and the tactic time, not the
`Qed`s, is the critical path.


---

## 2026-09-17 — array `len`/`cap`: fold the constant in Goose, and *also* add a guarded model rule

Fixing the array blocker needed a choice about where `len` of an array comes
from. Three options:

1. **A model rule only** — add `FuncUnfold go.len [go.ArrayType n t]` and
   leave Goose alone. This is what `bugs/goose-array-indexref-loads-its-operand.md`
   proposed, and **it does not work.** Goose emitted
   `FuncResolve go.len [T] #()` with *no operand applied*, so unfolding it
   yields a lambda that nothing applies and the surrounding
   `… ≥⟨go.int⟩ ![go.int] "n"` still compares against a closure. Rejected as
   insufficient, not merely inelegant.

2. **Goose emits the applied form, model rule discards the operand.** Works,
   but forces every array `len` to *load the whole array*, so a proof needs
   ownership of it — for `len(isLocalMsg)` on a package-level `[23]bool`,
   ownership of a global. Go's `len` needs neither, and `into_val_typed_array`
   (the array load lemma) is itself still `Admitted`, so this would have
   traded one blocker for another. Rejected.

3. **Goose folds the constant, and the model rule covers the rest.** Chosen.
   Go's own rule is that `len`/`cap` of an array is a constant expression
   unless the operand has channel receives or non-constant calls, and
   `go/types` already decides that for us: it records a `*types.Signature`
   for the builtin exactly when the call is *not* constant. So Goose branches
   on the thing the typechecker already computed, and emits
   `ctx.constantLiteral(s)` in the constant case. Every array `len` in the
   etcd code is constant, so the model rule has no consumer there — it exists
   for `len(f())` and so that the gap is actually closed rather than dodged.

The rule is **guarded**, `if decide (0 ≤ n < 2^63) then #(W64 n) else
AngelicExit #()`, matching `array_length_step` and `load_array` in the same
file. Unguarded it would be a false statement about Go for array lengths no
Go program can have. This is a trusted definition, so faithful-and-awkward
beats total-and-wrong.

The guard has a cost: `wp_auto` stops at the Gallina `if decide …`.
Rather than make every call site `case_decide`, the discharge lives once in
`new/golang/theory/array.v` as a `PureWp` whose side condition is
`0 ≤ n < 2^63` — the `pure_wp_slice_len` pattern, and the first non-trivial
`φ` in a `PureWp` here. `wp_pure` already runs `try done` on that side goal,
and for the literal lengths Goose emits, `done` closes it.

Two smaller calls inside this:

- The rules are stated at `st ↓u go.ArrayType n elem_type`, not at the
  literal `go.ArrayType`, so a **named** array type like
  `quorum.JointConfig` is covered. `new/golang/defn/map.v` declares its
  `FuncUnfold`s at the literal `go.MapType` and that is exactly why
  `wp_ProgressMap_len` exists as a workaround; not repeating it.
- `cap` is added next to `len` although nothing needs it, because the Go spec
  gives arrays the same answer for both and the missing half would resurface
  later as "stuck" with no hint as to why.

For the `len`/`cap` builtin emission, the case that should be impossible —
no signature *and* no constant value — is now `ctx.nope`, a loud translation
failure, rather than falling back to the old broken output. A full
re-translation of all five pinned repos never hits it.

## 2026-09-18 — every Go function gets a collection, axioms included, and a checker enforces it

**accepted.** Supersedes two paragraphs of the 2026-09-14 entry above: the
one that rejected putting the trust-boundary `wp_*` axioms behind Module
Types, and by extension the claim that an `Axiom` in an `inv_*.v` file is a
structural signal.

The 2026-09-14 refactor gave one collection to each of thirteen Go functions
and left **thirty-one others** stated as plain `Lemma`s and `Axiom`s in
`inv_misc.v`, `inv_raftlog.v`, `inv_tracker.v`, `inv_raft_phys.v` and
`inv_slices.v`. So the property the module system was adopted to enforce —
one Hoare triple per Go function, and no way to bypass it — held for `Step`
and its immediate callees and for nothing else. It had already failed twice
where it was not enforced: `raftLog.lastIndex` and `raftLog.lastEntryID` each
had two triples (see [false-statements.md](false-statements.md)).

**Decision:** a Hoare triple about a Go function lives in a
`spec_/postulates_/proof_/link_` collection, **whether or not it will ever be
proved**. Thirty-one collections added, `inv_slices.v` deleted (it held one
axiom and nothing else). The `inv_*.v` files keep what they were for:
ownership predicates, pure lemmas, `Ltac`, and interface contracts.

**Trust-boundary triples keep the `Axiom` keyword, inside the functor.**

    Module RaftAppendEntryProof (P : RAFT__APPENDENTRY_POSTULATES)
                                : RAFT__APPENDENTRY.
      Axiom wp_raft__appendEntry : wp_raft__appendEntry_body.
    End RaftAppendEntryProof.

Measured, not assumed: an `Axiom` inside an opaquely ascribed `Module`
discharges the signature's `Parameter`, and `Print Assumptions` on the
instantiated module still names it. So the accounting rule from
[STATUS.md](STATUS.md) survives the move unchanged — an `Axiom` means
*outside the raft protocol*, an `Admitted` means *in scope but unfinished* —
except that it is now read off the `proof_*.v` file rather than off which
`inv_*.v` file a declaration sat in. That is strictly better: the file name
now says which function, and the keyword says which kind of debt.

This is what the 2026-09-14 entry rejected, on the grounds that it "buys ~20
extra signatures for nothing" since nothing about those axioms will ever be
proved. That reasoning weighed only the *proving*. What the signatures
actually buy is the thing the refactor was for: `Include` makes a second
triple for the same function a build error, and opaque ascription means a
caller cannot reach around the spec. An axiom is a claim about a Go
function's behaviour, which is exactly the kind of claim this development
keeps getting wrong, so it is the last thing that should sit outside the
mechanism. Three of the eight false statements in
[false-statements.md](false-statements.md) were axioms.

**Rejected — a fifth file kind, `derived_<fn>.v`, for a weak corollary of a
spec.** Two functions wanted both an indexed `_at` triple and a weak one over
the existential `own_raftLog`. A functor from the signature to the corollary
would have served both without a second `Parameter`, but it adds a file kind
that the checker, `election.v` and every reader has to learn, against
`CLAUDE.md`'s "prefer a sentence in a markdown file over a mechanism".
Instead each function exports the one form its callers consume and the other
becomes a lemma inside the functor, hidden by the ascription — the same move
`Step`'s branch lemmas made on 2026-09-17. The one caller that then needed to
open `own_raftLog` got a two-line accessor, `own_raftLog_acc`, in the same
shape as the existing `own_raft_misc_option`. Details and the reason the two
functions went opposite ways are in
[false-statements.md](false-statements.md).

**The discipline is now checked, not remembered:**
`etc/check-module-discipline.py`. It matters *how* it checks. It does not
trust lemma names — it reads the program expression out of each triple
(`@! (go.PointerType raft.raft) @! "poll"`, `@! raft.newReadOnly`,
`functions slices.Sort`) and reports the Go function the triple really talks
about. That is what caught the two specs named after the wrong thing:
`wp_raft__appendEmptyEntry`, which specifies `appendEntry` and is named after
a method that does not exist in the generated code at all, and
`wp_campaign_peer_ids`, which specifies `quorum.JointConfig.IDs`. Both are
renamed. It also cross-references `new/code/` so that a spec naming a
function no generated package has is an error, and a spec naming a function
with no translated body is reported as information (that is
`slices.Sort` — it can only ever be assumed).

Interface methods are deliberately **not** treated as Go functions:
`wp_Logger__logf` and the three method specs bundled inside `is_Storage`
dispatch through `#(methods …)` on a client-supplied interface value, so
there is no Go function under verification to specify. They stay with their
predicate, and the checker reports them as `I-iface` information.

**Rejected — making the checker a hook or a CI job in this commit.** It exits
non-zero on errors so it can become either, but per `CLAUDE.md` only where
there is a demonstrated benefit; the benefit here is one run, already taken.
`notes/README.md` and this entry are the pointer. Wire it into CI when the
same violation comes back a second time.

**What is not fixed.** `readonly.v` has eight out-of-place triples and
`protocol.v` three, listed by
`etc/check-module-discipline.py` with no `--scope`. They were out of scope
for
this pass (the ask was the election proof) and `readonly.v` is a separate
development resting on `own_raft`, a second ownership story for the raft
struct. One of its triples duplicates an election spec for real — see
`raft.stepLeader` in [false-statements.md](false-statements.md).

---

## 2026-09-18 — a function's extra proof files go in `proof_<fn>_helpers/`

**accepted.**

With 44 collections the election directory holds 176 files that are four per
Go function, eight shared predicate/lemma files — and, before this, eight
more that were *neither*: `Step`'s branch lemmas
(`proof_raft__Step_MsgHup.v`, `_MsgVote.v`, `_MsgVoteResp.v`,
`_MsgVote_gt.v`, `_MsgVote_le.v`, `_MsgVote_lt.v`, `_MsgVote_eq_novote.v`,
`_MsgVote_eq_voted.v`). They sort in among the collections and look exactly
like collection members, so *listing the directory no longer told you what
was in it*: you could not see at a glance whether `proof_raft__Step_MsgVote`
was a Go function with a missing spec or proof structure with no spec by
design. That is a real auditing problem, because "does every triple about a
Go function have exactly one spec" is the property this layout exists to make
visible.

**Decision:** when one function's proof needs more than one file, the extra
files go in `proof_<fn>_helpers/`. The top level then holds exactly the four
files of each collection plus the shared files, and one directory per
function that has helpers. `Step` is the only such function today;
`proof_raft__Step_helpers/` holds its eight.

Nothing else changes: absolute logical paths mean the helpers' own
`Require Export …election.postulates_raft__Step` is untouched, and only the
three `Require`s *of* the moved files had to be retargeted.

**`proof_<fn>_helpers/` and not `proof_<fn>/`.** The latter is the obvious
name and it does not work: a directory `election/proof_raft__Step/` and the
file `election/proof_raft__Step.v` would both want the logical name
`…election.proof_raft__Step`. The `_helpers` suffix keeps the directory
sorting immediately after the file it belongs to, which is what makes the
listing readable.

**Rejected — shortening the file names inside the directory**
(`proof_raft__Step_helpers/MsgVote_gt.v`). It reads better in an `ls` and the
directory already supplies the context, but the journal's timing tables,
`gotchas.md` and `bugs/` all name these files, and the names are what someone
greps for after reading those. Not worth breaking for cosmetics; the
directory alone buys the auditability.

**Rejected — a single `helpers/` directory with per-function subdirectories.**
One entry at the top level instead of one per function, but it separates a
function's helpers from its collection, and with one such function today it
is speculative structure.

**Enforced, not remembered.** `etc/check-module-discipline.py` gained three
checks: `H1`, a proof helper at the top level (detected structurally — a
`proof_<X>_<suffix>.v` whose collection has no spec while `<X>` does — not
from a list of known filenames); `H2`, a `Module Type` or an assumption
inside a helpers directory, which would mean a spec is hiding in proof
structure; and `H3`, a helpers directory with no `proof_<fn>.v` to help. All
three were checked by planting a violation and watching them fire.
`--summary` now also lists which functions have helper directories, so the
answer to "whose proof spans several files" is one command rather than an
`ls` and a guess.

**The checker knows the toolchain, not this development.** Worth stating
because the first cut did not: it had the package name `raft` in its naming
policy, fixed paths for the proof and code roots, a hardcoded table of scope
names, and a code index that dropped Rocq's module alias on the grounds that
"these five packages are distinctive enough". All four are gone. What it
knows now is Goose's rendering of a call, Perennial's `{{{ … }}}` notation
and the file-naming convention, each named in a constant at the top of the
file — plus two overridable defaults for where this repository keeps its
proof and its generated code.

Concretely: the naming check accepts *either* a bare name or a
package-prefixed one (`Sort` or `slices_Sort`) rather than privileging one
package, since deciding which package is "the" one under verification is
exactly the judgement a checker should not be making; the code index resolves
the alias a proof writes against the `Module` declarations of the generated
files, so a package translated to a file of any name resolves correctly;
`--scope` takes a path or the bare name of any directory under the proof
root; and `--proof-root` aims the whole thing elsewhere. Demonstrated rather
than asserted: pointed at `new/proof/go_etcd_io/etcd`, a development that
predates the convention entirely, it reports 24 out-of-place triples.

---

## 2026-09-18 — what the TCB *is*, and a tool that measures it

**accepted**

Counting the trust base by hand did not scale and was not honest. `STATUS.md`
carried two greps with the caveat that "both over-count", a table of axioms
maintained by editing, and a count of `Admitted`s that had to be re-derived
every time a file moved. The 2026-09-18 restructure moved every triple into a
collection and the counts had to be redone from scratch to show that it had
*not* changed the trust base.

**Decision:** `etc/tcb-report.py`, and a definition of the TCB with three
parts rather than one.

1. **assumed** — an `Axiom`/`Parameter`/`Conjecture`/`Hypothesis` outside a
   `Module Type`, and every proof ending in `Admitted`.
2. **results** — the statements the development exports.
3. **definitions** — everything those statements are written in terms of,
   transitively.

The third is the part a count of axioms misses, and here it is the biggest:
85 definitions and 651 lines against 45 assumptions and 127 lines. A theorem
is only as good as its definitions — `raft_election_safety` says nothing if
`own_raft_ghost` or `nstate.t` is wrong, and neither is an axiom.

**And what is deliberately not in it.** A `Parameter` inside a `Module Type`
is discharged by the functor ascribed to that signature; 44 of them, none
assumed. The spec of a function something else in the development calls is an
untrusted proof artifact: if it is wrong, its callers' proofs fail. That is
the distinction the module discipline was built for, and this is what makes
it visible — 43 of the 44 collections are internal, and exactly one,
`raft__Step`, is exported.

**Externally facing = nothing in the development depends on it.** A
collection no *other collection* requires or names, or a declaration in a
file nothing requires that nothing else names. Two things this got wrong on
the way:

- **Rejected — Go's export rule (a capitalised name) as the decision.**
  `quorum.JointConfig.IDs` is exported from its package and is an internal
  callee here; `raft.raft.poll` is unexported and would be exported if the
  proof stopped at it. Whether Go exports it is reported next to each result,
  because a result that is *unexported* in Go is worth a second look, but it
  does not decide.
- **Re-exporting is not calling.** The first cut counted `election.v`'s
  `Require Export link_*` — which exists so that `make ci` builds them — as a
  use, which made every collection look internal and left the development
  with no exported result at all. Only a require or a mention from another
  *collection* counts.

**Rejected — `Print Assumptions` as the source of truth.** It is the right
answer and it is not available: over a `.vos` tree it sees axioms reachable
from statements but not what opaque proofs used, so the `Admitted`s and the
`wp_*` trust-boundary axioms do not appear at all. Ground truth needs a full
`.vo` build of Perennial, which nothing in this tree has. A syntactic tool
that runs in 0.4s and can be pointed at any subtree is what the inner loop
needs; when a `.vo` build exists, `Print Assumptions` should be used to check
*this* tool, not the other way round.

**Rejected — making it a CI gate.** `etc/check-module-discipline.py` is the
gate and has a crisp pass/fail. "The TCB grew" is not a defect: it grows when
an axiom is converted into a real definition with `Admitted` methods, which
is the conversion working. The tool always exits 0.

**What it cannot see, stated in the tool's own docstring.** References
through a `Notation`, and instances found by typeclass resolution rather than
named, are invisible; definitions from Perennial, stdpp and Rocq are outside
the tree and are not counted, though they are trusted too and are far larger
than anything measured here. So the definition count is a lower bound, and
`--view surface` prints how many names it could not resolve so that the
reader can judge how much is missing.

**The parser is now shared.** `etc/rocqscan.py` holds what both tools need —
where a sentence ends, what it declares and inside which modules, how a proof
ended, and which Go function a triple's program expression names — with its
own `--selftest`. It was lifted out of `check-module-discipline.py`, whose
output on all of `--scope election_proof`, the whole raft tree and `--format json`
is byte-identical before and after. One parsing contract was the point: it is
the part most likely to rot, and two copies would rot apart.

**Consequences:** the numbers in `STATUS.md` are now printed rather than
maintained, and the hand-written table of axioms is a *why* column for a list
the tool produces. The two hand counts it replaced were right — the tool
reproduces 6 axioms and 7 `Admitted`s on the election path, and 14
`Admitted`s over the whole raft proof, which is what the notes said.

## 2026-09-20 — an upper bound on the log length is derived, never carried

**Decision.** `own_raftLog_at` keeps `Hnowrap : prev.index + |sents| + |uents| + 1 < 2^64`
exactly as it was, and no spec above `appendEntry` gains a no-wrap premise.
The bound `appendEntry` needs *after* appending is derived from two facts
that survive the append: `is_Storage`'s new persistent pure clause
`Hbounded` (the client's stable log ends below `2^61`; `prev.index + |sents|`
is untouched by an append) and `|uents| < 2^63`, which `own_slice_len`
re-derives for whatever slice the Go `append` returns. Their sum clears
`2^64` with room for a batch of up to `2^61`, which is the third premise of
`wp_raft__appendEntry`.

**Why not the plan the task described** (thread a premise
`appendEntry → becomeLeader → stepCandidate → Step`). A premise of
`becomeLeader` or `Step` may mention only `cfg, r, id, s`; the log's length
is existentially quantified *inside* `own_raft_phys`, so no premise at those
specs can speak about it. Threading would have meant indexing
`own_raft_phys` by the last index (95 call sites) or exposing it in every
spec up to `Step`.

**Why not a tighter carried bound** (the "fixed slack" variant, e.g.
`Hnowrap` at `2^63`, which a concurrent agent briefly tried for `extend`).
`append` grows `uents`, so the conjunct must be *re-established* at the new
length, and from `last + 1 < C` one cannot get `last + |ents| + 1 < C` for
any `C`. A carried bound can only ever be consumed, never restored. Any
proof that needs `|sents| + |uents| < 2^63` (Go `int` arithmetic in
`extend`/`slice`) has to get it from the slice `slice` returns — `hi - lo` at the `slice`
call plus `Hbounded` plus the unstable slice's own length — not from
`own_raftLog_at`.

**Consequence for the trust base.** `Hbounded` is a new clause of the
`Storage` interface contract, i.e. an assumption about client code. It is
the assumption that makes appending possible at all, and it is stated once,
in `inv_storage.v`, with the justification at the clause.

## 2026-09-20 — the tracker predicates expose their values, and the progress map is read-only

Forced by `bcastAppend`, whose `Visit` closure calls back into the raft
struct (`r.sendAppend(id)`), and by three tracker methods that panic.

- **`own_inflights_at l iv`, `own_progress_at pr pv iv`** (with the old
  `own_inflights`/`own_progress` as their existential closures), plus the
  pure invariants `inflights_ok` (the ring buffer: `Add` writes
  `buffer[(start+count) mod size]` after growing on demand, and with
  `start=100, count=0, size=1000, buffer=[]` it is "not full", grows to one
  slot and indexes slot 100 — without the invariant `Add`'s triple is
  false), `inflights_full`, and `progress_state_ok` (`IsPaused` panics
  outside Probe/Replicate/Snapshot; `SentEntries` outside Probe/Replicate).
  `own_tracker` gained `HmaxInfl : 0 ≤ MaxInflight < 2^62`, the premise
  `NewInflights` now takes. These conjuncts exist to make triples *true*,
  not merely stronger.

- **The progress map is `↦$□` (`DfracDiscarded`).** `maybeSendAppend` holds
  the raw `pr` pointer across `r.send(...)`, which consumes and rebuilds the
  whole tracker under an existential, and must then call `pr.SentEntries`
  on *that* pointer. With an exclusive, existential map there is no way
  back to it; a discarded-fraction map is duplicable, so `prs !! to = Some pr`
  survives the rebuild (`own_tracker_lookup`, via a new `progress_map_agree`
  for `own_map` — provable in the framework, since the pure map is a
  function of the stored `val`; lift it into `theory/map.v` when a second
  caller appears). Honest under the election scope: nothing inserts into
  or deletes from `trk.Progress`, only `Progress` *values* are written.
  **Cost**: a future reconfiguration proof must take the map back to
  `DfracOwn 1`.

- **`visit_closure cfg trk votes f I` is existential in the tracker value.**
  `own_raft_phys` hides the struct value, so a closure that re-enters the
  struct (every triple below `raft.send` is on `own_raft_phys`) merges the
  lent `trk ↦ tv` back into `r ↦ rv` and gets a fresh, existential `rv'`
  back; nothing says `rv'.(trk') = tv`, because `send`'s *spec* cannot say
  it does not touch the field. So the closure returns
  `∃ tv', trk ↦ tv' ∗ own_tracker cfg tv' votes ∗ I`, `Visit`'s loop
  invariant carries a moving `tv'`, and `reset`'s closure keeps
  `raft_split_trk`'s quantified continuation wand in its `I`.

- **`is_Storage` gained `HSnapshot`** (either `ErrSnapshotTemporarilyUnavailable`
  or a snapshot with `Metadata.Index ≠ 0`; any other error or an empty
  snapshot panics), because the snapshot fallback is *reachable*: nothing in
  `own_progress` bounds a peer's `Next` against the log, so
  `raftLog.term(pr.Next-1)` may return `ErrCompacted`. That is also why
  `raftLog.term`'s partial triple has to become total (STATUS item 15).

## 2026-09-21 — `own_raft_bare`: the struct predicate with the tracker and the log split out

**Superseded by** "2026-09-22 — Three layers, and one ownership predicate per
object" below: `own_raft_bare`, `own_raft_notrk` and `own_raft_phys_at` are
gone, and what they said is now in `nstate.t` (`progress`, `log`, `lent`,
`stepfn`).

**Decision.** `inv_raft_phys.v` gains `own_raft_bare r id s f tv lg` — every
conjunct of `own_raft_phys_at r id s f` except `Htrk` and `Hlog`, plus
`rv.(trk') = tv` and `rv.(raftLog') = lg` — with `own_raft_notrk` the
tracker-only wrapper (`∃ lg, own_raft_bare … ∗ own_raftLog lg`) and
`own_raft_phys_at_split : own_raft_phys_at r id s f ⊣⊢ ∃ tv, own_raft_notrk r id s f tv ∗ own_tracker cfg tv s.(nstate.votes)`.
`raft.send` is specified on `own_raft_bare`; `maybeSendSnapshot` on
`own_raft_notrk ∗ own_progress pr`. `own_raft_phys` itself is unchanged,
so its ~21 other spec files are untouched; the conjunct list is spelled
out twice on purpose, with a "keep in step" warning, because folding one
through the other would put two existentials in front of every existing
`iNamed "Hphys"`.

**Why.** `maybeSendAppend` reads a `Progress` pointer and borrows the
entries `ents` out of the log *before* `r.send(...)`, and needs both
*after* it (`pr.SentEntries(len(ents), payloadsSize(ents))` follows the
send in the Go). A `send` specified on `own_raft_phys` demands the whole
struct — tracker and log included — and returns it under `∃ rv'`, so the
caller can neither hold what it borrowed nor re-find it. `send` in fact
touches only the two message queues; the spec now says so by carrying
`tv` and `lg` through. The general rule is in false-statements.md
(2026-09-21): a borrow out of `P` must come back out of `P`'s
*precondition*, not be re-derived from its postcondition; making the
borrowed thing persistent fixes re-finding, not holding.

**Rejected.** Keeping `own_raft_phys` in `send`'s spec and threading the
tracker value as an extra postcondition equation (`rv'.(trk') = rv.(trk')`)
— it does not help with `ents`, which cannot even be *held* across a
call that demands `own_raftLog`. Indexing `own_raft_phys` by the tracker
and log values everywhere — 95 call sites for no gain above `send`.

---

## 2026-09-21 — the result is verified specs for top-level raft functions; election safety is not the payoff

This answers what `STATUS.md` carried as open next step #5, "decide what the
top-level Raft correctness statement should be".

**The object of study is code.** What this development is for is a Hoare
triple on each function an etcd caller actually calls — the `node` interface
(`Propose`, `Ready`, `Advance`, `Step`, `Campaign`, `Tick`) and `raft.Step`
beneath it — each saying what running that Go function does to the state it
owns. That is the deliverable, and it is the only thing a client of this
proof consumes.

**`raft_election_safety` is not the payoff.** It is an internal lemma, and
calling it the payoff — which `election.v`, `election_proof/protocol.v`,
`raft-election-refinement.md` and `raft-proof-map.md` all did until today —
gets the shape of the work backwards. Delete the corollary and no
verification claim about etcd's code is weaker; delete `wp_raft__Step` and
there is nothing left. The protocol layer of `election_proof/protocol.v`, the
refinement obligation and the whole election development exist **in service
of** the function specs: they are how a triple about `Step` gets to say
something stronger than "the struct fields changed".

What the corollary is genuinely for is a **sanity check on the model** — it
shows that `nstate.t` and `step` are strong enough to entail the property
raft exists to provide, which is evidence the abstraction was not defined
into triviality. That is worth having. It is not the result.

**Consequences, in the order they bite:**

1. **What belongs on the exported surface is the function specs.** Since
   2026-09-23 `etc/tcb-report.py --view surface` has two sections: *results*
   — Go-function Hoare triples nothing else in the development calls, which
   for the election development is `wp_raft__Step_body` alone — and *root
   lemmas*, stated facts nothing uses yet, which is where
   `raft_election_safety` lives. Root lemmas are neither results nor counted
   in the TCB. (Until then the tool promoted any unused theorem in a file
   nothing required, and once `--scope` became a dependency cone that put
   the corollary on the surface.)

   **A root lemma is not therefore disposable.** `raft_election_safety` is
   today the *only* user of `own_raft_ghost_is_leader` and
   `is_leader_unique`, and that pair is what will stop the ghost state being
   built trivially. Without it, `own_raft_ghost γ id s` := a per-`id`
   exclusive token that ignores `s`, with `is_message` := `True`, satisfies
   every other axiom in `Section ghost` — and is allocatable, so it is a real
   model that certifies nothing. With it, that model fails: `step` has a win
   transition, so two nodes could each step into Leader in the same term. A
   construction therefore has to track leadership per term against vote
   quorums, which is what forces `is_message` to certify votes. Until a spec
   consumes the corollary — proposal or commit, which rely on a single
   leader, are the likely ones — its real job is keeping that obligation
   alive. (`own_raft_ghost_excl`, by contrast, is used by nothing at all.)

   **Update, 2026-09-22:** the ghost state was then constructed on `main`
   (`7cb3d419d`), and took exactly the shape this paragraph predicted the
   uniqueness pair would force — each node's vote history in a ghost map,
   held to one vote per term (`vote_hist_ok`); `is_message` certifying only
   a granting `VoteResp`; `is_leader` a quorum of votes — with
   `own_raft_ghost_alloc` showing it inhabited. The pair are lemmas now, so
   the corollary no longer keeps an *axiom* alive. It is still their only
   user, and `own_raft_ghost_excl` is still used by nothing.

   Independently of all this, the `Step` proof is not trivial: the ghost
   predicates are opaque, so every branch has to go through
   `own_raft_ghost_step` and prove the code's transition is a `step`. The
   uniqueness pair is what makes that relation worth being refined.
2. **A protocol-level property earns its place only when a function spec or
   its client needs it.** Do not add protocol theorems for their own sake.
3. **"Is the proof done?" is answered by reading the triples**, not by
   counting theorems or admits — which is the same point
   [tcb-accounting.md](tcb-accounting.md) makes from the tooling side.
4. The corollary cannot even do its sanity-check job while the ghost state is
   axiomatized: with no allocation axiom for `own_raft_ghost`, the trivial
   model satisfies every axiom in the `Section ghost` block and the corollary
   holds vacuously. Constructing that ghost state (next step #4) is what
   turns the check into a real one.
5. **The top-level statement is still owed for the rest of the `node`
   interface.** `v3.v` covers `Propose`; `protocol.v` axiomatizes `Ready` and
   `Advance`. Those triples, discharged against the translated code, are the
   remaining shape of the answer — not a new theorem above them.

---

## 2026-09-22 — the election proof gets its own directory, beside the old one

`new/proof/go_etcd_io/raft/v3_proof/` had become two unrelated developments
in one directory: the leader-election refinement (the current work, 332
files) and the earlier read-index/heartbeat proofs (`protocol.v`,
`readonly.v`). The election work is now `raft/election_proof/`, a **sibling**
of `v3_proof/` rather than a subdirectory of it.

**Layout**, flattened — there is no `election_proof/election/`:

    raft/v3.v                     the old public surface
    raft/v3_proof/base.v          IsPkgInit boilerplate, required by BOTH
    raft/v3_proof/protocol.v      old: axiomatized node interface
    raft/v3_proof/readonly.v      old: read-index work (and unbuilt -- STATUS)
    raft/election_proof/election.v      aggregator + raft_election_safety
    raft/election_proof/protocol.v      the model (was election_protocol.v)
    raft/election_proof/{defs,step_lemmas,inv_*}.v
    raft/election_proof/{spec,postulates,proof,link}_<fn>.v
    raft/election_proof/proof_<fn>_helpers/   (two today: raft__Step,
                                               MajorityConfig__VoteResult)

**Why a sibling and not a subdirectory.** The old name said the election
proof was part of the `v3_proof` development, and it is not: it shares
`base.v` with it and nothing else. Nesting it also made every logical path
carry two directory levels that meant nothing
(`…raft.v3_proof.election.spec_raft__Step`), and it put the old proofs in
the way of anyone reading the new tree.

**Why the aggregator lives inside.** `election_proof/election.v` rather than
a sibling `election_proof.v`, so that the whole development is one directory
and `ls` of `raft/` shows two developments rather than two developments and
a loose file. The cost is that `etc/tcb-report.py`'s cone cannot find the
aggregator by the `v3.v`/`v3_proof/` convention and seeds from every file in
the directory instead; that gives the same cone, and the docstring says so.

**Why `base.v` stayed.** Both developments require it, and it is
package-init boilerplate rather than proof. Moving it would have made the
old tree depend on the new one, which is backwards; copying it would have
left two lists of `IsPkgInit` instances to keep in step.

**The cost, paid once.** 332 files moved and 709 lines of references
rewritten across `.v`, `.md` and `etc/*.py`, verified statically: every
`Require` in the raft tree resolves through `_RocqProject`'s load paths to a
file that exists (703 require targets), nothing outside `journal.md`
mentions the old paths, both self-tests pass, and
`etc/check-module-discipline.py --scope election_proof` exits 0. Two
requires in `should_build.v` do not resolve in `rocqscan`'s model
(`New.proof.Import`, `New.proof.leasing_proof.protocol`); both are
pre-existing parse gaps on lines this did not touch. **Then built**, at
`454e0d780`: the `.vos` closure (471 files) and `.vok` of all 336 raft files,
0 errors — details in `STATUS.md`.

**Regenerated, not rebased.** The move was first made against a `main` that
had 184 election files. Branch `worktree-election-close-admits` then landed
on `main` with 330, 140 of them new, plus a second helper directory. A
replayed rename would have moved the old 184 and left the new 140 behind
with `Require` paths pointing at a directory that no longer existed. So on
rebasing, this commit was **regenerated** by re-running the move and
reference-rewrite scripts on `main`'s actual tree — the right treatment for
any mechanical refactor that meets new files. The scripts move every `.v`
file and every subdirectory rather than a named list, which is what caught
`proof_MajorityConfig__VoteResult_helpers/`.


## 2026-09-22 — Three layers, and one ownership predicate per object

**Decision.** The development is a refinement in three layers, and each has
its own state type:

1. **Go code and heap → physical abstract state.**  `own_raft_phys r id s`
   (`election_proof/inv_raft_phys.v`) relates the raft struct and everything
   hanging off it to `s : nstate.t` (`election_proof/defs.v`).  Every Go-level
   spec is a pre/postcondition pair on `own_raft_phys`.  This is the layer
   the current work is on.
2. **Physical state → protocol state.**  `nstate_rel s ps`
   (`election_proof/defs.v`) relates `s` to the protocol state `ps : pstate.t`
   (`election_proof/protocol.v`): `ps` is `s`'s six protocol fields
   (`to_pstate s`), `r.step` agrees with the role, and nothing is on loan.
   `Step`'s spec (`election_proof/spec_raft__Step.v`) is the only statement that
   mentions both layers.
3. **Protocol state → protocol properties.**  `own_raft_ghost γ id ps`,
   the transition relation `step`, and `raft_election_safety`, all about
   `pstate.t` and free of Go.

**The rule this entails, and which is now written into
`election_proof/defs.v`, `election_proof/inv_raft_phys.v`, STATUS.md and
gotchas.md:** `nstate.t` is the *most abstract* description of the physical
state that still lets *every* Go-level WP be stated on `own_raft_phys`.
**If a function cannot be specified with `own_raft_phys`, refine `nstate.t`
(and `own_raft_phys` with it) until it can.  Do not add a variant
predicate** — a second ownership predicate for the same struct, or the
same one with an extra parameter, or a spec on raw pieces of it
(`r ↦ rv ∗ own_tracker …`) — for one caller's benefit.  The same goes for
every other object: one ownership predicate, indexed by an abstract state
precise enough for all of that object's methods.

**What this replaced.** Until 2026-09-22 one record, `nstate.t` in
`election_proof/protocol.v`, served as *both* the physical abstraction and the
protocol state, so anything the Go specs needed that the protocol did not
have to be carried outside it.  That produced three variant predicates
for the raft struct, each added to unblock one caller:

- `own_raft_phys_at r id s f` — `r.step` as a free parameter, because
  `becomeFollower` writes `r.step` *before* `reset`, so mid-function the
  field and the role disagree (2026-09-16).  Specs of `reset`, and
  `maybeSendSnapshot`'s, were stated on it.
- `own_raft_bare r id s f tv lg` and `own_raft_notrk r id s f tv` — the
  struct with the tracker and/or the log cut out, and their field values
  pinned as parameters, so that `maybeSendAppend` could hold a `Progress`
  and `ents` across `r.send` (2026-09-21, entry above).  `send` and
  `maybeSendSnapshot` were stated on them.

and five `raft` methods specified on raw pieces (`abortLeaderTransfer`,
`resetRandomizedElectionTimeout`, `increaseUncommittedSize` on `r ↦ rv`;
`promotable`, `hasUnappliedConfChanges` on `r ↦ rv` plus the tracker or the
log).  Every caller had to convert into and out of each of these.  All are
gone: the physical `nstate.t` is a new record with the six protocol fields
(same names) plus

- `stepfn : func.t` — `r.step`, literally;
- `progress : gmap w64 loc` — the progress map, pinned by a persistent
  conjunct of `own_raft_phys`, so a proof can return a borrowed `Progress`
  before a call and re-borrow it at the same key afterwards
  (`maybeSendSnapshot` is stated this way);
- `log : loc` — `r.raftLog`, pinned;
- `lent : option tracker.ProgressTracker.t` — the tracker's heap and the
  log are **on loan to the caller** (`Some tv`: `own_raft_phys` owns
  neither and pins `r.trk = tv`).  `maybeSendAppend` sets it across
  `r.send` (it needs the *same* `Progress` facts after the send, and
  `ents`); `appendEntry` across `increaseUncommittedSize` (it holds the log
  open at a fixed split).  A function that touches either says
  `s.(nstate.lent) = None`; the top-level ones say `nstate_wf s`.
  Superseded 2026-09-29: the log now holds its entries read-only; see
  inv_raftlog.v, own_unstable. (`lent` now loans only the tracker.)

and the protocol record in `election_proof/protocol.v` became `pstate.t`, with
its functions prefixed `p` (`psend_msgs`, `pbecome_follower`, …,
`pcan_vote`, `init_pstate`).  The physical ones keep the old names, so
spec text such as `own_raft_phys cfg r id (become_follower s t l)` reads as
before but now also says what `r.step` becomes.  Each physical transition
commutes with its protocol counterpart under `to_pstate` by computation
(`to_pstate_become_follower` etc., `defs.v`), and the `Step` proof uses
exactly those equations to move from one layer to the other.

**Why.** A variant predicate is a second specification of the object's
state, and every one of them was a place where two callers disagreed about
what the struct is.  `own_raft_phys_at` could not be stated at the call
site that needed it next (`newRaft`, whose struct has a nil `r.step`) without
adding a fourth.  The refinement picture also says where the information
belongs: "`r.step` is `stepFollower`" and "the log is held by the caller"
are facts about the physical state, and the protocol has no business
carrying them, so they cannot be protocol fields — but the Go specs need
them, so they are physical-state fields.

**Rejected.**
- *Adding `stepfn` to the protocol record.*  The model would then have to
  name the raft package's `stepX` functions, and every protocol transition
  would have to say what `r.step` becomes.  The ghost state has no use for
  it.
- *`stepfn : option role.t` instead of `func.t`.*  Considered, and not what
  was asked for; `func.t` is exact and costs nothing at this layer.
- *Handing the borrowed `Progress` back before `send` and re-borrowing it
  afterwards.*  Works for re-finding the pointer (which is why
  `nstate.progress` exists), but not for `maybeSendAppend`: the
  re-borrowed `Progress` comes back as `∃ pv iv`, and `SentEntries` needs
  the facts about `pv`/`iv` the proof established *before* the send.
  Hence the loan.
- *A loan of just the slice `entries` returns* (`option (slice × dfrac × list Entry)`).
  Tried first; it does not cover `appendEntry`, which needs the whole log
  at a fixed split across a call, nor the tracker half of
  `maybeSendAppend`.

**Then done for the log** (2026-09-23, entry "One predicate per object"
below): the log's three shapes — `own_raftLog` (existential split),
`own_raftLog_at` (indexed by the split) and the raw
`l ↦ lv ∗ (… -∗ own_raftLog_at …)` that `raftLog.entries`/`slice` returned —
are one predicate indexed by `logstate.t`.

**The trace hooks** (amended 2026-09-23).  The six `traceX` hooks take `r`
and were specified on raw pieces -- five on `own_raft_misc`, the struct's
miscellaneous conjunct, and `traceReplicate` on the entries slice.  The
first version of this entry left them alone, on the grounds that moving
them to `own_raft_phys` would cost a re-seal (fold the opened predicate
back up) and a reopen at every call, several inside the most expensive
`Step` helpers.  That was the wrong comparison: their translated bodies are
`do: #()`, so the honest spec owns **nothing**
(`{{{ is_pkg_init raft }}} … {{{ RET #(); True }}}`), which obeys the rule
and costs callers nothing.  They are stated that way now.  Only true of
the no-op build that is translated; the tracing build reads `r`.

## 2026-09-23 — One predicate per object, below the raft struct too

**Context.** "Three layers" gave the raft struct one predicate. Asked
whether anything else owned the same state twice or in several shapes, the
answer on the election path was yes, five times: `own_raft_phys` carried a
persistent copy of the progress map's points-to (`#Hprs`) beside the one
inside `own_tracker`; `Progress` and `Inflights` each had an indexed form
(`own_progress_at`, `own_inflights_at`) and an existential one, and
`Inflights.grow`/`reset` and `Progress.ResetState` were stated on raw
points-tos; the log had three shapes; the `unstable` specs were on raw
`u ↦ uv ∗ entries ↦* uents`; and `newReadOnly`'s postcondition was stated
on more than the object it returns.

**Decision.**
- `own_tracker cfg tv votes prs`, indexed by the progress map; the copy in
  `own_raft_phys` is gone. The `Visit` closure hands the tracker back at the
  same `prs`.
- `own_progress pr pv iv` and `own_inflights l iv buf` are the only forms.
  `buf` is in `Inflights`' index because `grow` is specified by what it does
  to the buffer; `Progress` quantifies it (no `Progress` method reads it).
- `own_raftLog l (ls : logstate.t)`, `ls` = entry list, `committed`,
  `applied`, and `page : option (slice × list Entry × dfrac)`. **A loan is a
  field of the state**: `raftLog.slice`/`entries` return the log at
  `ls <| page := Some (s, es, dq) |>` with the lent slice outside, and
  `own_raftLog_return_page` ends the loan. The struct `l ↦ lv` stays
  outside the loan's wand so `maybeSendAppend` can read `committed` with a
  slice lent out (`own_raftLog_struct`). Every other `raftLog` spec takes
  `ls.page = None`.
- `own_unstable u uv uents page` for the embedded `unstable`, with its own
  loan (`unstable.slice`). The `raftLog` proofs assemble it from the
  field points-to and the entries.
- `newReadOnly` returns only `own_read_only ro`; `own_raft_misc` is built on
  it and `own_raft_misc_swap` installs the new one.

Superseded 2026-09-29: the log now holds its entries read-only; see
inv_raftlog.v, own_unstable. (`logstate.page` and `own_unstable`'s `page`
argument are gone.)

**The log's state is not in `nstate.t`.** The rule for the raft struct
says the state must be precise enough for every spec. No election-path
spec on `own_raft_phys` needs to relate the log's state across a call --
each function that uses the log opens it, works at a fixed `ls`, and closes
it -- so `own_raft_phys` keeps `∃ ls, ⌜ls.page = None⌝ ∗ own_raftLog l ls`.
Moving `ls` into `nstate.t` is the fix the rule prescribes the first time a
spec needs it; `newRaft`'s postcondition (which has to say what log it
built) is the likely first.

**Alternatives considered.** Stating the `raftLog` specs at the components
(`own_raftLog l (logstate.mk prev sents uents cm ap None)`) needs no `page = None`
premise and no `destruct` in the proofs, but reads worse at every spec and
every caller holds an abstract `ls`. The `page = None` premise as a Coq premise
costs an explicit state at positional calls (gotchas.md).

## 2026-09-24 — Program proofs do not unfold `own_raft_phys`

**Context.** "Three layers" (above) made `own_raft_phys r id s` the one
ownership predicate for the raft struct, but every program proof still
opened it: `iNamed "Hphys"` to get `r ↦ rv` and the abstraction relation,
`wp_auto` for the field accesses through `r ↦ rv`, then a re-seal with
`own_raft_phys_intro` before each callee and an `iNamedSuffix` after it --
about thirty opens and thirty re-seals across the election proofs,
`campaign` and the `Step_MsgVote_*` helpers worst. So the predicate was an
abstraction in the specs only; the representation was written into every
proof, and changing it meant touching all of them.

**Decision.** `own_raft_phys` is sealed (`own_raft_phys_def` +
`seal`, `election_proof/inv_raft_phys.v`) and program proofs reach the struct
only through the interface at the end of that file:

- **One Hoare triple per field load and per field store**, stated at the
  expression `wp_auto` leaves behind: `![t] #(r.[raft.raft.t, "f"])` and
  `GoStore t (#(r.[raft.raft.t, "f"]), #v)%V`.  A field `nstate.t` tracks is
  loaded at its abstract value and a store updates the state
  (`wp_raft_store_Term : … {{{ own_raft_phys r id (s <| nstate.term := v |>) }}}`);
  a field pinned by a scope assumption is loaded at the pinned value
  (`checkQuorum` at `false`); an untracked field is loaded at an unknown
  value (`∃ v`) and stored freely.  That last point is why the index did not
  have to grow to every scalar field: if a proof needs two loads of an
  untracked field to agree, the usual rule applies -- add it to `nstate.t`.
- **Accessors for heap hanging off a field** -- the tracker, the log, the
  two message queues, the `readOnly` object: a wand lemma hands out the
  field's points-to and the object's own predicate, and takes them back
  (possibly changed) for `own_raft_phys` at the correspondingly changed
  state.  **Map accesses go through the accessor, not through per-operation
  lemmas**: `r.trk.Progress[i]` is a lookup on the tracker object
  `own_raft_phys_tracker` hands out, done with the tracker's own lemmas.
  (The alternative -- a triple for `map.lookup1 … (![T] #(r.[trk].[Progress])) #i`,
  another for insert, another for delete -- duplicates the map API for one
  field path.)  The message queues' accessors are append-only: the wand
  takes back `ms ++ ms'` and grows the abstract outbox by `ms'`.
- **Loans** (`nstate.lent`, "Three layers") get `own_raft_phys_lend` /
  `own_raft_phys_unlend`, and `own_raft_phys_trk_lent` reaches the tracker
  field while the tracker is out.  The last two are stated at the setter
  form `s <| lent := Some tv |>`, because `(s <| lent := x |>).(lent) = x`
  does not typecheck by `eq_refl` for a variable `s`.

**No search tactic, no `wp_auto` for raft fields.**  Each proof names the
lemma for each access: `wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"`.
A first version had `wp_raft_field`, which tried the ~25 field lemmas in
turn; every failed `wp_apply` walks the whole program expression, which on
the `Step` bodies is the slow part of a proof, and a proof that names its
lemma says which field it touches.  (Its 110 call sites were replaced
mechanically: the tactic was instrumented to print the lemma each site
used, every proof was run once, and each site was rewritten to that
sequence.)  `wp_raft_log` survives because it is a fixed sequence -- slice
literal, `r.logger` load, `wp_Logger__logf` -- with no search; the loads of
a log call's arguments are written out before it.

**Rejected.**
- *`AccessStrict` instances on `own_raft_phys`, so `wp_auto` handles field
  accesses as it does for `r ↦ rv`.*  `wp_auto`'s field automation is built
  on full ownership of the struct, which is the abstraction this predicate
  exists to replace, and an instance would need every field's value to be
  a function of the index -- the whole struct in `nstate.t`.
- *Leaving the predicate unsealed and relying on convention.*  One
  `iNamed "Hphys"` in a new proof would quietly bring the representation
  back; sealed, it does not compile.

## 2026-09-29 — The log's state is in `nstate.t`

**Context.** Since 2026-09-23 `own_raft_phys` quantified the log's state
(`∃ ls, … own_raftLog l ls`), and `nstate.lent` loaned tracker and log
together to callers that had to hold the log at a known state across a
call. Asked to move the log's state into `nstate.t` and work towards
removing `lent`.

**Decision.** `nstate.logst : logstate.t`; `own_raft_phys` owns the log at
it, always; a slice lent by `raftLog.slice`/`entries` is recorded in
`logst.page`, not outside the predicate. Transitions that change the log say
how (`become_leader` appends `leader_entry s`), so specs up the call chain
(`poll`, `stepCandidate`, `Step`) did not change shape.

**Consequences.** Specs are more precise (`appendEntry`'s old postcondition
at the same `s` was only true because the log was hidden). The cost is that
a proof can no longer hold the log across a field load or callee: it takes
it out and puts it back around each access (`own_raft_phys_log_same`).
`lent` remains, for the tracker only; see STATUS item 2.

Superseded 2026-09-29: the log now holds its entries read-only; see
inv_raftlog.v, own_unstable. (Later the same day: `logst.page` is gone,
and `slice`/`entries` hand out their result read-only and for good.)

## 2026-09-29 — The log holds its entries read-only; no slice is lent

**Context.** `logstate.page` recorded a slice `raftLog.slice`/`entries`
had handed out while it shared memory with the log, with a wand back in
`own_raftLog`. It was the last non-physical field of the log's state, and
`nstate.t` is to have only physical fields.

**Decision.** `own_unstable` and `own_raftLog_core` hold the unstable
entries at `↦*□`, with the capacity slack owned (`own_slice_cap`);
`unstable.slice`, `raftLog.slice`/`entries` and `scan` hand out their
result `↦*□`, and the log comes back unchanged; `is_Storage`'s `Entries`
returns `↦*□` with no wand. `logstate.page`, `own_unstable`'s `page`
argument and the lend/return lemmas are deleted.

**Why it is true of the code** (upamanyus/etcd-raft, 531b20c): no element
of `u.entries` is ever written in place (`log_unstable.go`: every
assignment re-slices, copies, adopts, or appends past `len`; the
truncating append goes through the cap-limited `u.slice`,
`log_unstable.go:228-234`); `raftLog.slice` re-caps its unstable result
(`log.go:508`); `extend` writes in place only into `cap(dst)` slack
(`util.go:318-319`), which `is_Storage`'s `cap = len` rules out; and
`Storage.Entries`' documented contract forbids mutating returned entries
(`storage.go:56-67`), which `MemoryStorage` honours (`storage.go:155`,
`:303-305`).

**Consequences.** The `append` in `truncateAndAppend` needs a destination
held read-only: `wp_slice_append_persistent`
(`new/golang/theory/slice.v`, next to `wp_slice_append`).
`is_Storage` is a stronger assumption than before (read-only for good
rather than lent), but it is the interface's own. `maybeSendAppend`'s
`MsgApp` may keep aliasing `ents` in `r.msgs` without the proof tracking
it. `raftLog.slice`'s proof got ~15% slower (605s → 709s), from re-sealing
the log at each of its seven exits. Known gap, not on the election path:
`nextUnstableEnts` returns an uncapped slice (todo.md).

**Rejected.** *A `pin` field recording a `Progress` value, for the
tracker loan* — not physical state; `nstate.t` holds only physical fields.

## 2026-09-29 — Each peer's `Progress` value is in `nstate.t`; nothing is ever lent

**Context.** `nstate.lent : option ProgressTracker.t` let a function take
the tracker's heap out of `own_raft_phys` for its whole body, so it could
hold a `Progress` across a call on the struct. `reset`, `maybeSendSnapshot`
and `maybeSendAppend` used it. A proposed replacement, a `pin` field
recording one `Progress` value, was rejected: it is not physical state.

**Decision.** `nstate.prvals : gmap w64 (Progress.t * Inflights.t)`, each
peer's `Progress` and `Inflights` values; `own_tracker cfg tv votes prs pvs`
pairs `prs` and `pvs` key by key (`big_sepM2`). `lent`, `nstate_idle`, the
lend/unlend lemmas and every `nstate_idle s` premise are deleted;
`nstate_wf` is just the `r.step` equation. Specs of functions that write a
`Progress` quantify the new values in the postcondition (`{{{ pvs, RET …;
own_raft_phys (X <| nstate.prvals := pvs |>) }}}`) rather than computing
them: `reset`'s would need `MaxInflight` and the log's last index, and no
caller looks.

**How each former loan went.** `reset`: `Visit`'s invariant is the wand of
`own_raft_phys_tracker_prvals` (as `bcastAppend` already did), and the
closure re-seals whenever it needs the whole struct and re-borrows `pr` at
the recorded value. `maybeSendSnapshot`: borrows `pr` at each of its two
accesses. `maybeSendAppend`: borrows `pr` around each stretch that touches
it (`own_raft_phys_pr`/`_upd`/`_any`); `SentEntries`' premises survive
`r.send` because the state records `pr`'s value and `send` changes only the
outbox. This is the one function that needed the values in the state.

**Rejected.** *A pin* (above). *Keeping `lent`* — a loan is not state of
the Go program. *Computing the new values in the transitions* — more
precision than any caller uses, at the cost of more fields
(`MaxInflight`).
