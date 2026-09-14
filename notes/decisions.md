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
