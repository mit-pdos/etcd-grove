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
  `election_protocol.v` had one; `base.v`, `protocol.v`, `readonly.v` and
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
`readonly.v:51`), `is_quorum` twice (`election_protocol.v:84` vs
`readonly.v:114`), and `readonly.v` axiomatizes `own_raft` as a second,
incompatible ownership story for the struct `own_raft_phys` already covers.

**Decision:** four files per Go function, under `v3_proof/election/`, modeled
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
supports the same payoff theorem.

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
