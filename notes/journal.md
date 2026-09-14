# Journal

Dated log, newest last, append-only. Read `STATUS.md` for orientation; come
here to answer "how did this get this way?"

Per entry: what changed (with paths), anything surprising, **what was tried and
did not work**, and the state left behind. Never rewrite an earlier entry — if
one turns out to be wrong, say so in a later one.

---

## 2026-09-11 — Fork setup: de-perennialize the repo, start the notes

Claude Opus 5 (background job), at Upamanyu's request.

- **Did:**
  - Retargeted repo identity to `upamanyus/etcd-grove`: README rewritten around
    the etcd goal (CI badge now points at this repo's Actions), `perennial.opam`
    homepage/bug-reports/dev-repo/maintainer/description, `flake.nix`
    description, `pyproject.toml` name, `docs/opam.md` wording,
    `CONTRIBUTING.md` retitled.
  - Fixed CI: every workflow triggered on `master`, but this fork's default
    branch is `main`, so **CI had never run here**. `ci.yml`, `goose.yml`,
    `nix.yml` now trigger on `main`.
  - Deleted workflows that only made sense upstream: `mailbot.yml` (emailed the
    whole PDOS team on every push), `update-tested.yml` (pushed a `coq/tested`
    branch for Rocq's CI), `opam-update.yml` (needs a `secrets.PAT` this fork
    does not have), `dependabot-automerge.yml` (relied on an upstream repo
    ruleset to gate merges on CI — without it, it would auto-merge unverified
    dependency PRs). `dependabot.yml` itself was kept; its PRs now need manual
    review, and `CONTRIBUTING.md` says so.
  - Deleted upstream-only scripts: `etc/popl21-supplement/` (POPL'21 artifact),
    `etc/release.sh` (perennial release tarball; referenced `.travis.yml` and
    `etc/ci`, neither of which exists any more), `etc/split-repo.fish` (one-off
    helper for splitting `pav` out of upstream; its own comment said to delete
    it once used).
  - Corrected stale `CONTRIBUTING.md` claims found along the way: it pointed at
    `src/ShouldBuild.vo`, `etc/update-goose.py` and `etc/ci-use-goose-pr`, none
    of which exist; the real entry points are `new/should_build.v` and
    `new/etc/update-goose-new.py`.
  - Created this `notes/` tree, rewrote `AGENTS.md`, symlinked `CLAUDE.md` to
    it. Added a `SessionStart` hook, a `Stop` hook and a `/notes` skill — all
    since removed, see the next entry.
- **Learned:** the etcd work was already substantial before the fork —
  `new/proof/go_etcd_io/raft/v3_proof/readonly.v` is 955 lines of protocol
  development, and `new/etc/update-goose-new.py` already pointed at
  `upamanyus/etcd-raft` and `upamanyus/etcd`. Written up in
  `raft-proof-map.md` and `goose-workflow.md`.
- **Dead ends:** considered renaming the Go module path and the Rocq
  `Perennial` logical path to match the fork, and decided against both — see
  `decisions.md`. Worth reading before anyone tries the sweep again: ~71 files
  for zero benefit to the etcd proofs, and a conflict on every upstream merge.
- **Found, not fixed:** `ruff check` reports 64 pre-existing errors, all in
  files unrelated to this work (see "Known broken" in `STATUS.md`). Left alone
  deliberately — 47 are auto-fixable but `PLW1510` changes `subprocess.run`
  semantics. It will turn the `python` CI job red on the first push to `main`.
- **Left:** no `.v` files touched, so the Rocq build is unaffected.

## 2026-09-11 — Rip out the hooks; flatten notes to plaintext

Claude Opus 5, on Upamanyu's correction.

- **Did:** deleted `etc/agent-notes/session-start.py`,
  `etc/agent-notes/stop-check.py`, `.claude/settings.json` and the
  Claude-Code-specific `/notes` skill. Flattened `notes/` from 11 files across
  four directories to 7 flat markdown files, dropping the three
  scaffolding-only `README.md` index/template files. Moved the "update the
  notes before you finish" instruction into `AGENTS.md` and
  `notes/README.md`, where any agent will read it.
- **Learned — the standing principle here:** *only add structure where there is
  a demonstrated benefit.* The hooks failed it twice over: they were
  Claude-Code-specific in a project that will use other agents, and they
  automated a step nobody had yet been observed to skip. Recorded in
  `decisions.md` and in `notes/README.md`, since it should govern future
  additions too.
- **Left:** notes are `STATUS.md`, `gotchas.md`, `raft-proof-map.md`,
  `goose-workflow.md`, `decisions.md`, `journal.md`, `README.md`. Nothing
  enforces that they get updated; that is deliberate. Still no `.v` changes, so
  the Rocq build is untouched.

## 2026-09-11 — Merged the fork setup onto `main`

Claude Opus 5.

- **Did:** fast-forwarded `main` onto the setup branch, then merged
  `origin/main`, which had picked up PR #2 (`actions/setup-go` 6 → 7) in the
  meantime. One conflict: `.github/workflows/opam-update.yml`, modified there
  and deleted here — kept deleted. `ci.yml` and `goose.yml` auto-merged, taking
  both the `setup-go@v7` bump and the `master` → `main` trigger fix.
- **Learned — the dependabot auto-merge risk was real, not hypothetical.** PR
  #2 was auto-merged into this fork's `main` by `dependabot-automerge.yml`
  **with no CI run at all**. Verified: at commit `8222672f6`, `ci.yml`'s
  `pull_request` trigger filtered on base branch `master`, so a PR against
  `main` never triggered it, and upstream's GitHub Ruleset (which is what gates
  the auto-merge on passing CI) does not exist on this fork. So the workflow
  was merging dependency bumps blind. Deleting it was right; the earlier entry
  described this as a risk, and this is it happening.
- **Left:** `main` carries the fork setup and is pushed. The `python` CI job is
  expected to go red on this push — see "Known broken" in `STATUS.md`.

## 2026-09-12 — leader-election refinement, first pass

- **Did:** added `new/proof/go_etcd_io/raft/v3_proof/election_protocol.v` (the
  protocol state machine for leader election, the `own_raft_ghost` /
  `is_message` ghost state and its one refinement obligation) and
  `.../election.v` (`own_raft_phys`, the helper-axiom trust boundary, and the
  `raft.Step` triples). Both reached from `new/should_build.v`. Scope: no
  pre-vote, no proposals, no read-only, no reconfiguration. Full write-up in
  [raft-election-refinement.md](raft-election-refinement.md).
- **Proved:** `wp_raft__send_vote` (the one that matters — it is where the
  "every message on the network is protocol-legal" obligation is discharged),
  `wp_raft__Step_MsgHup`, `wp_voteRespMsgType`, the five model-level
  step-composition lemmas, the `wp_raft__Step` dispatch, and
  `raft_election_safety`. `wp_raft__Step_MsgVote` is proved through the term
  preamble, the step-down and its ghost transition, and the `canVote`
  computation.
- **Ten lemmas remain `Admitted`**, listed in priority order in the topic file.
- **Design decision worth keeping:** the log is absent from the protocol model.
  `isUpToDate` can only make a node *decline* to vote, and declining is always
  protocol-legal, so the model has a `step_reject_vote` rule with no premises
  and never needs to talk about logs. This is what makes the model small
  enough to be worth having.
- **Design decision, second:** `step` is reflexive-transitive by construction.
  Without that, `campaign` (which becomes a candidate *and* broadcasts) would
  not refine a single transition.
- **Dead end, recorded:** `own_raft_misc` was first indexed by the whole
  `raft.raft.t`, which forced an `own_raft_misc rv -∗ own_raft_misc rv'` axiom
  to survive any field write — an axiom strong enough to be worthless. Now
  indexed by the three fields it actually covers. Don't go back.
- **Stuck point:** `wp_raft__Step_MsgVote`'s `send` of the granted vote. The
  ghost step produces exactly the right `is_message`, but `iFrame` will not
  place it into `wp_raft__send_vote`'s precondition, and restating that
  precondition in explicit `msg.mk` form did not help. Not diagnosed; the
  topic file says what to try next.
- **Environment:** this ran on a machine with no Rocq at all. Built an opam
  switch from `perennial.opam`'s pins (~1h). Set up
  [rocq-warm](https://github.com/zeldovich/rocq-warm), which turned a ~3 min
  cold check of `election.v` into 1–20 s replays and is the only reason the
  code-level proofs got as far as they did. The flags it needs against a `vos`
  tree are in [gotchas.md](gotchas.md), along with two other traps this
  session hit (`word` on `w32` disequalities, and `wp_slice_literal` leaving
  `go.array_literal_size` unreduced).

## 2026-09-13 — a trust-base reader for the raft proof

Claude Opus 5 (background job), at Upamanyu's request.

- **Did:** added `etc/tcb-view.py`, which renders Rocq files down to their
  trust base — top-level theorem statements, the transitive closure of the
  definitions those statements mention, and every `Axiom` and `Admitted.` —
  hiding proof bodies and proved helper lemmas. Plain text to stdout, stdlib
  only, no build required. Rationale and the rejected alternatives are in
  [decisions.md](decisions.md).
- **The inventory it reports**, which is now the answer to "what does the raft
  proof assume": 46 axioms — 22 in `election.v` `Section helper_axioms`, 11 in
  `election_protocol.v` `Section ghost`, 6 in `protocol.v` (4 in `Section
  axioms`, plus `node.t` and `message.t`), 7 in `readonly.v` — and 17
  `Admitted.`, of which 2 are deliberate (`readonly.v:469,478`, marked
  `(* Trusted *)`) and 15 unfinished, containing 12 interior `admit.` tactics
  between them. `./etc/tcb-view.py --summary new/proof/go_etcd_io/raft` prints
  it.
- **Found by using it:** `election.v` had 24 axioms two commits ago and has 22
  now — `a9027f994` dropped `is_TraceLogger`/`is_TraceLogger_pers` and renamed
  `is_Logger_ok` to `is_Logger`. That the diff of two revisions' output is
  readable at all is the main argument for plain text over HTML.
- **Learned — what the corpus actually contains.** The six raft files use no
  `Notation`, no `Program`/`Next Obligation`, no nested comments and no
  `Definition := ltac:(...)`, which is why a hand-written tokenizer is enough.
  The hazards that do bite: `{{{ ... }}}` Hoare triples start 62 lines in
  `election.v` and appear *inside* `Axiom` statements; `Set Default Proof
  Using "W"` is a line containing `Proof` that does not open one; proofs end in
  `Defined.` twice; `Admitted. (* Trusted *)` and plain `Admitted.` are
  textually identical apart from that comment and mean opposite things.
- **Dead end:** `.glob` would have been the better foundation — it is free
  output of every build, byte-offset addressed, and knows about typeclasses,
  which a name-based closure cannot. It is unusable here because it is
  gitignored and only exists for files built to `.vo`; four of the six raft
  files had none. Do not restart down that path without first checking
  `find new/proof/go_etcd_io/raft -name '*.glob'`.
- **Tried and rejected:** a separate `etc/test_tcb_view.py`. `etc/test_coqc.py`
  is the cautionary case — nothing runs it and it no longer imports (`from
  coqc import ...`; the module is now `rocqc.py`). Correctness went into
  `./etc/tcb-view.py --self-check` instead, which checks byte-exact round trip
  over all 547 `.v` files in the repo plus the counts above, and the round trip
  is asserted on every ordinary run too.
- **Left:** the tool and the notes. No `.v` file was touched. The natural
  follow-on is a `Print Assumptions` cross-check, which is the only way to see
  assumptions inherited from Perennial/Iris/Goose; it needs a built `.vo`, so
  it did not fit the "works on any checkout" constraint this tool was built to.
