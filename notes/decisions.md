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

## A textual trust-base reader, `etc/tcb-view.py`

**2026-09-13 · accepted**

Reviewing what the raft proof *assumes* meant reading 2429 lines of Rocq across
six files and filtering out the proofs by eye. The trust base is currently 46
`Axiom`s and 17 `Admitted.`s in four files, and nothing listed them in one
place. `notes/STATUS.md` already carried two roadmap items about discharging or
justifying those axioms, and `raft-proof-map.md:77-79` already said "anything
not proved should be either discharged or explicitly justified here" — so the
need was recorded before the tool was; this is not speculative structure.

**Decision:** one stdlib-only script, `etc/tcb-view.py`, that renders a `.v`
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

**No separate test file.** Correctness lives in `./etc/tcb-view.py
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
in `inv_*.v`.

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

**Consequences.** 51 files where there was one. `election.v` is a 78-line
aggregator that `Require Export`s every `link_*.v`; that is load-bearing,
because `make ci` builds only what `new/should_build.v` reaches, so a link
file nothing re-exported would silently go unchecked. The trust base is
unchanged — 49 axioms, 14 `Admitted` — and is now split structurally: an
`Axiom` in `inv_*.v` means *out of scope*, an `Admitted` in `proof_*.v` means
*in scope but unfinished*.

**Superseded within the same day:** the first cut gave `Step` four spec files
(one per message type plus the dispatch). Upamanyu pointed out that this is
four Hoare triples for one Go function, i.e. exactly what the refactor exists
to prevent. The three per-message-type triples are proof structure and are now
internal lemmas inside `proof_raft__Step.v`, sealed by the ascription. **If a
function ever seems to want two specs, that is the signal to look harder, not
to add a second `Module Type`.**

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
