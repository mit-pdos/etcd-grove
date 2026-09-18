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

## 2026-09-14 — the three `becomeX` lemmas

Claude Opus 5 (background job), at Upamanyu's request: "prove the admitted
`wp_raft__become<foo>` lemmas". Branch `worktree-raft-election-refinement`.

- **Did:** `wp_raft__becomeFollower`, `wp_raft__becomeCandidate` and
  `wp_raft__becomeLeader` in
  `new/proof/go_etcd_io/raft/v3_proof/election.v` are now `Qed`. They still
  *call* `wp_raft__reset`, which remains `Admitted` — that was the given
  interface and it was left alone. Raft trust base went 46 axioms / 17
  `Admitted.` → 50 / 14.
- **Shape of each proof.** `wp_auto` walks the whole function body except
  three places: the `bool_decide` guarding the panic arm (rewrite it false
  from the role hypothesis), the call to `reset` (re-seal `own_raft_phys` and
  `wp_apply`), and the variadic logger argument (the
  `wp_slice_literal` dance). The postconditions come out as literally the
  model's `become_follower` / `become_candidate` / `become_leader`, which is
  the point — those definitions were written to mirror the Go code and they
  do.
- **`becomeCandidate`/`becomeLeader` panic arms.** `becomeCandidate` panics
  on `state == StateLeader` and `becomeLeader` on `state == StateFollower`.
  Both discharge from the role hypothesis via
  `destruct (s.(nstate.role)) eqn:Hro; try congruence` — the `eqn:` matters,
  since plain `destruct` does not substitute into the hypothesis that rules
  the bad case out. `word` will not close `W64 0 ≠ W64 2`; the
  `f_equal uint.Z; vm_compute; discriminate` idiom already in the file does.
- **`becomeLeader` needed the trust boundary widened**, by four axioms:
  `own_progresses`, `own_progress_rest`, `wp_tracker_progress_lookup`,
  `wp_Progress__BecomeReplicate`, plus a (non-axiom) `own_progress`
  definition and a new `own_progresses r.trk.Progress` conjunct in
  `own_raft_phys`. `becomeLeader` does
  `pr := r.trk.Progress[r.id]; pr.BecomeReplicate(); pr.RecentActive = true`,
  and the existing opaque `own_tracker` could not produce any of it. The
  reasoning behind the exact shape (keyed on the map reference, `own_progress`
  a definition so the inline field assignment has real ownership) is in
  [raft-election-refinement.md](raft-election-refinement.md); the short
  version is the same rule the `own_raft_misc` note already states — index it
  by what it actually covers.
- **`wp_raft__becomeLeader` gained a hypothesis, `id ∈ cfg`**, because only
  voters are in `trk.Progress`. Its first caller will be
  `wp_stepCandidate_MsgVoteResp`, which will have to thread it in.
- **Found: `own_raft_phys` claims `r.trk` twice.** `trk` is an embedded
  `tracker.ProgressTracker` *value*, so `r ↦ rv` covers its bytes, and
  `own_raft_phys` *also* holds
  `own_tracker (struct_field_ref raft.raft.t "trk" r)`. Harmless today
  because `own_tracker` is an opaque axiom that need not own anything;
  fatal the moment someone constructs it, since `own_raft_phys` would become
  provably `False` and every `Step` triple vacuous. Written up in the topic
  file and added to `STATUS.md`'s next steps. Not fixed here — fixing it
  means deciding what `own_tracker` is, which is step 3.
- **`reset` is not as mechanical as the previous note claimed.** Besides
  re-initialising every `Progress` through `trk.Visit`, it replaces
  `r.readOnly` with a fresh `newReadOnly(...)`, and `own_raft_misc` is
  indexed by the old pointer — so it needs a `wp_newReadOnly` axiom. Noted in
  the topic file so the next person does not rediscover it mid-proof.
- **Method.** `election.v` is now 1045 lines and a cold check is ~3 min, so
  the three proofs were developed in a throwaway
  `v3_proof/scratch_become.v` = `head -<reset's Admitted> election.v` + the
  lemma under construction, which cold-checks in 45 s and replays in 3–15 s
  under `rocq-warm`. Splice back and check the real file once at the end.
  That is worth reusing; the deleted scratch file is not worth keeping.
  Three tactic traps this cost time on are now in
  [gotchas.md](gotchas.md).

## 2026-09-14 (later) — fix the `own_tracker` duplication

Claude Opus 5 (background job), same session as the entry above, at
Upamanyu's request: "fix the own_tracker duplication".

- **The bug.** `own_tracker` was indexed by a **location**, and
  `own_raft_phys` instantiated it at `struct_field_ref raft.raft.t "trk" r`
  while also holding `r ↦ rv`. `trk` is an embedded `ProgressTracker`
  *value*, and `r ↦ rv` is *by definition* (the `TypedPointsto` instance in
  `new/generatedproof/go_etcd_io/raft/v3.v:1175`) the conjunction of the
  field points-tos, `r.[raft.raft.t, "trk"] ↦ rv.(trk')` among them. So the
  tracker's bytes were claimed twice. Undetectable while `own_tracker` is an
  opaque axiom; `own_raft_phys` would have become provably `False` the moment
  anyone constructed it.
- **The fix.** `own_tracker : tracker.ProgressTracker.t → gmap w64 bool →
  iProp Σ` — indexed by the tracker *value*, owning only what the value
  points at (the map at `Votes`, the map at `Progress` plus the `Progress`
  objects, the id sets of `Config`). Disjoint from `r ↦ rv` by construction.
  This is the rule the `own_raft_misc` note in the topic file already stated:
  index it by what it actually covers.
- **Knock-on changes.** `ResetVotes` / `RecordVote` / `TallyVotes` now take
  `trk ↦ tv` as well, because a mutating method needs the location, and
  `ResetVotes` genuinely assigns a fresh map to `p.Votes`
  (`tracker.v:947`) — so it returns `trk ↦ (tv <| Votes' := votesRef |>)`.
  `own_raft_phys` lost a conjunct: the `own_progresses` predicate added
  earlier today for `becomeLeader` is now just part of `own_tracker`, and
  `wp_tracker_progress_lookup` reads the map reference out of `tv`. Raft
  trust base 50 axioms → 49.
- **Two more latent errors fell out**, both from axioms that had never been
  applied. `wp_raft__promotable` quantified over an `id`, a `trk` and an `l`
  with nothing tying them to the `r` it was a method on; it is now stated
  against `r ↦ rv`, `own_tracker rv.(trk')` and
  `own_raftLog rv.(raftLog')`, concluding
  `b = bool_decide (rv.(id') ∈ cfg)`. And `wp_campaign_peer_ids` used one
  `loc` as both the tracker (`own_tracker trk votes`) and the tracker's
  `Voters` field (the `*quorum.JointConfig` receiver of `IDs`), which cannot
  both hold; the receiver is now
  `trk.[ProgressTracker.t, "Config"].[Config.t, "Voters"]`, matching what
  `campaign` actually calls (`new/code/go_etcd_io/raft/v3.v:3817`).
- **Cost: none in the proofs.** All three `becomeX` proofs and
  `wp_raft__send_vote` went through unchanged apart from dropping the
  now-redundant `Hprog` from the re-seal selectors. The reason is that
  `own_tracker rv.(raft.raft.trk')` frames through a record update
  (`(rv <| step' := _ |>).(trk')` reduces to `rv.(trk')`) exactly the way
  `own_raft_misc rv.(readStates') …` already did — that clause was the
  precedent that made this safe.
- **For whoever finishes `reset` and `poll`:** to hand `trk ↦ tv` to a
  tracker method while holding the whole struct, split the field out with
  `iEval (rewrite typed_pointsto_unseal /typed_pointsto_wrap /=) in "Hr"`.
  `wp_auto` does not need this — it goes through the generated
  `AccessStrict` instances — only an explicit `wp_apply` does.


## 2026-09-14 — election.v split into one file per function

Refactor, no new proof content. `election.v` 1072 → 78 lines; 51 new files
under `v3_proof/election/`. Rationale, alternatives and the enforcement
mechanism are in [decisions.md](decisions.md); this is the log.

- **One semantic change, done first and alone.**
  `wp_stepCandidate_MsgVoteResp` gained `id ∈ cfg`. It mentioned no `cfg`,
  but its eventual proof must call `wp_raft__poll` (which mentions `cfg`) and
  `wp_raft__becomeLeader` (which takes `id ∈ cfg` outright). That was free
  while `cfg` was a section variable; inside a proof functor there is no
  ambient `cfg` to reach for. Everything after this was mechanical.
- **Order:** shared non-module files → `voteRespMsgType` (leaf, to pin the
  shape) → `reset`/`becomeFollower` (first real postulate) → the rest up the
  call graph → aggregator.
- **The trust base is unchanged: 49 axioms, 14 `Admitted`,** identical to the
  pre-refactor numbers, re-partitioned into `inv_*.v` (out of scope) and
  `Admitted` in `proof_*.v` (unfinished). Plus 11 module-type obligations —
  one per Go function, which is the one-spec-per-function invariant made
  countable.
- **`Step` initially got this wrong.** The first cut gave it four spec files,
  one per message type plus the dispatch. Upamanyu caught it: four Hoare
  triples for one Go function is the thing the refactor exists to prevent, and
  the header comment calling it "layering" did not make it not a duplicate.
  The three branches are now internal lemmas in `proof_raft__Step.v`. Twelve
  files removed. `grep -l Step spec_*.v` is now exactly one file.

### Traps this cost time on

- **`.vos` does not check proof bodies.** It is a fine 2-second loop for
  statements, signatures and module structure, and it will happily accept a
  proof script that does not run. Use `make <file>.vok` for the real check —
  about 60s per function. A `.vo` build is not an option: nothing in the tree
  has `.vo` deps, so `make x.vo` starts building all of Perennial.
- **`Print Assumptions` over a `.vos` tree under-reports** and is not ground
  truth. It lists axioms reachable from *statements* (`own_raftLog`,
  `own_tracker`, `own_raft_ghost`) but not what opaque proofs used, so the
  `Admitted`s and the `wp_*` trust-boundary axioms do not appear. Confirming
  the trust base by `Print Assumptions` needs a full `.vo` build. Until then
  `./etc/tcb-view.py` plus the `vok` sweep is what we have.
- **`Collection W` is section-scoped; the `Set` naming it is not.** A closed
  lemma placed after `End <section>` fails with `Unknown variable: W`, and
  forcing W's variables into it would add binders its signature does not have.
  `proof_raft__Step.v` restores `Set Default Proof Using "Type"` after the
  section for exactly this reason.
- **Implicit arguments are not inferred through a folded `_body`**, so
  `Vrmt.wp_vrmt MsgVote eq_refl` fails with `The term "MsgVote" has type
  "w32" while it is expected to have type "ffi_syntax"`. One `Arguments` line
  per link file fixes it; inside the `Module Type` it is accepted but does not
  survive functor application.
- **`Require` is illegal inside a `Module` or `Section`**, so a spec file that
  needs `New.proof.bytes` (for `wp_Equal`) must `Require Export` it — `Import`
  does not reach the proof file.
- **Watch for prefix collisions when renaming**: `wp_raft__Step_MsgVote` is a
  prefix of `wp_raft__Step_MsgVoteResp`, and a naive ordered replace mangles
  the longer one.

### `etc/tcb-view.py`

Taught it that a `Parameter` inside a `Module Type` is an obligation, not an
assumption — without this the refactor read as 49 axioms → 63. The scope
tracker now tells `Module Type FOO` from `Module FOO` (it recorded both as
`Module FOO`). `--self-check` gained two fixtures and, more usefully, checks
the invariant directly: **every `spec_*.v` must declare exactly one
`Parameter` and assume nothing**. That is self-maintaining, unlike a
hard-coded list of file names.

## 2026-09-15 — ambient binders: implicits kept, `intros` de-fanged

Follow-up to the one-file-per-function split. No proof content changed; the
trust base is still 49 axioms / 14 admitted / 11 obligations.

- **`Arguments` moved from the 11 `link_*.v` files into the 11 `Module Type`s.**
  It propagates to every implementing module, functor application included, so
  the spec file is now the single place both the triple and its implicit
  convention are declared.
- **`bytes_sem` deleted.** `raft.Assumptions` carries
  `#[global] import_bytes_Assumption :: bytes.Assumptions`, so it resolved from
  `package_sem` all along (as `package_sem.(raft.import_bytes_Assumption)`).
  It was only ever in `spec_raft__Step.v`; removing it makes `package_sem` the
  last ambient binder everywhere.
- **`intros ?????? sem package_sem …` replaced by `intros_ambient`**, one Ltac
  in `election/defs.v`. The list of ambient binders now exists in one place, so
  a change to it is one edit rather than eleven.

### Two of my own claims were wrong; both are corrected in place

- **"An `Arguments` inside a `Module Type` does not survive functor
  application."** False, and it was the reason the lines were in the link files
  at all. It was a **`grep` artifact**: the printed
  `Arguments Vrmt.wp_voteRespMsgType {ext ffi …}` wraps across three lines and
  the pattern used to check it kept only the first, so it read as empty.
  Re-tested untruncated against the real environment: the implicits were there
  all along.
- **"Do not delete these lines; they are load-bearing."** Also false. Every
  call site in the tree goes through `wp_apply (P.wp_<fn> with "…")`, which
  unifies the arguments itself; deleting an `Arguments` line and re-running
  `vok` on a caller passes. Verified by doing exactly that, then reverting.
  The lines are worth keeping for direct application and readable `About`
  output, but nothing here depends on them.

### `intros until package_sem` looks right and is not

Worth recording because it is an attractive trap. It is insertion-robust and
needs no `rewrite`, so it survived a deliberate `extra : nat` injected ahead of
`package_sem` — but a binder that does not occur in the rest of the statement
**loses its name**: Rocq degrades `∀ (x : T), body` to `T → body`.
`package_sem` occurs in `becomeLeader`'s statement but not in
`voteRespMsgType`'s, where the same tactic fails with `No quantified
hypothesis named package_sem in current goal even after head-reduction`. Five
of the six proofs passed and one did not, which is exactly the shape of bug
that gets mistaken for something else. Bare `intros` and `intros *` are wrong
for their own reasons; all of it is written up once in
[gotchas.md](gotchas.md).

Also tested and rejected: making `_body` a `Notation` so the implicits are
inferred syntactically. The generalized binders still come out explicit.

## 2026-09-15 (later) — the outbox moves into `nstate.t`; no internal spec touches ghost state

Started as a question: why does `wp_raft__campaign_body` carry
`own_raft_ghost` when `wp_raft__becomeLeader_body` carries only
`own_raft_phys`? The rule was real but nowhere written down:

> A spec carried `own_raft_ghost` iff the function could put a message on the
> network.

Because `own_raft_phys` required both outgoing queues to hold only *certified*
messages (`is_phys_msg`), `send` demanded `is_message` for the message it was
handed; the only producer of `is_message` was `own_raft_ghost_step`, which
hands out tickets only as part of advancing the ghost state. So a function
that sends had to take its ghost step in its own body. `campaign` broadcasts,
so it needed the ghost; `becomeLeader` does not send anything the model
describes, so it did not.

That was already "ghost as high as possible" in the part that matters —
`becomeLeader`'s triple never claimed `s → become_leader id s` was a *legal*
step, only that the struct refines it — but the ceiling was the innermost
function containing a `send`.

### What changed

`nstate.t` gained an `outbox : list msg.t` field, and `step` lost its `sent`
output: a step's sent messages are now the growth of `s'.(nstate.outbox)`.
Consequences, all in the same direction:

- `own_raft_phys` lost its `γ`. `is_phys_msg` was its only use of one, so the
  predicate is now genuinely ghost-free and "phys-only spec" is literally true
  rather than a manner of speaking.
- The certification clause became `own_raft_ghost_outbox`, a new axiom in
  `election_protocol.v`: `own_raft_ghost γ id s -∗ [∗ list] m ∈ s.(nstate.outbox), is_message γ m`.
  Nothing has to be threaded through specs to get it.
- `send` lost its `is_message` precondition and is routing-agnostic: one
  postcondition covers both queues.
- `campaign`, `hup` and `stepCandidate` are ghost-free. `stepCandidate` also
  lost its `is_message` premise outright — its ghost use was purely
  receive-side, and the receive side only ever fed the fupd.
- `Step` is the only spec that mentions ghost state, and the only proof file
  that applies `own_raft_ghost_step`. Its postcondition got *simpler* (the
  `sent` existential is gone).
- `step_trans` got easier for the same reason — the outbox accumulates through
  the intermediate state instead of needing `o₁ ++ o₂` bookkeeping.

`reset`, `poll`, `becomeFollower`, `becomeCandidate` and `becomeLeader`
changed only by dropping `γ`. That is the point: those specs were already
right.

### The encoding, and why it is what it is

`own_raft_phys` relates the model's single outbox to the two physical queues:

    ⌜ s.(nstate.outbox) ≡ₚ abs_outbox msgs msgsAA ⌝

with `abs_outbox msgs msgsAA := omap abs_msg_opt msgs ++ omap abs_msg_opt msgsAA`.

- **`omap`, not `mapM`.** A message type the model does not describe drops out
  instead of making the abstract outbox undefined. This is load-bearing; see
  the axiom fix below.
- **`≡ₚ`, not `=`.** Appending to `msgs` does not append to the concatenation
  when `msgsAA` is non-empty, so equality would not survive a `send`.
  Permutation is also all the model needs — it cares which messages are out,
  not in what order.

`proof_raft__send_vote.v` was the gate on this encoding and it went through
with three one-line helpers in `defs.v` (`abs_outbox_snoc_msgs`,
`abs_outbox_snoc_msgsAA`, `abs_outbox_snoc_msgsAA_None`). Permutation
reasoning did not turn out to be a tax; the fallback of two `nstate` fields
plus plain equality was not needed.

### A false axiom, found and fixed

`wp_raft__appendEmptyEntry` had pre- and postcondition `own_raftLog l` — it
owned the log and nothing else. But `appendEntry` ends in

    r.send(pb.Message{To: r.id, Type: pb.MsgAppResp, Index: li})

(`new/code/go_etcd_io/raft/v3.v`, end of `raft__appendEntryⁱᵐᵖˡ`), which
appends to `r.msgsAfterAppend` — memory the axiom did not own and its caller,
`becomeLeader`, did via `own_raft_phys`. **The axiom was false**, and it let
`becomeLeader` keep a stale `HmsgsAA`.

It could not have been stated honestly under the old design:
`mtype_of MsgAppResp = None`, so `is_phys_msg γ` was *unprovable* for that
message and the `#HsentAA` clause could never have been re-established. With a
partial `abs_msg_opt` and `omap`, the honest statement is expressible and
trivial — the message drops out of the abstract outbox, so the state is
unchanged:

    Axiom wp_raft__appendEmptyEntry : ∀ r id s es,
      {{{ is_pkg_init raft ∗ own_raft_phys r id s }}}
        r.appendEntry(es)
      {{{ RET #true; own_raft_phys r id s }}}.

It moved from `inv_misc.v` to `inv_raft_phys.v`, since it now has to mention
`own_raft_phys`. Still an `Axiom` in an `inv_*.v` file, so the audit
convention still reads correctly.

### A drain rule, so the model is not quietly contradictory

`step_drain s o' : o' ⊆+ s.(nstate.outbox) → step s [] (s <| outbox := o' |>)`.
Without it the model's outbox could only grow, and `own_raft_phys` could not
refine past the first `Ready()`. `Ready` is out of scope, but the rule is one
line and removing the latent contradiction now is cheaper than discovering it
later. Dropping messages from one's own outbox is always legal — the
`is_message` facts handed out for them are persistent and survive.

### Two things that bit

- **stdpp renamed `elem_of_list_lookup_2` to `list_elem_of_lookup_2`** (and
  `elem_of_list_lookup{,_1}` likewise). The error is
  `The variable elem_of_list_lookup_2 was not found in the current environment`,
  which reads like a missing `Require`. Grepping the stdpp sources for the old
  name finds nothing; `Search (_ ∈ _) (_ !! _ = Some _)` in a scratch file
  compiled with `-Q src Perennial -Q new New` finds it in seconds. Also in
  [gotchas.md](gotchas.md).
- **`wp_apply … as` runs `wp_auto` immediately**, so re-sealing
  `own_raft_phys` around a call whose *continuation* reads struct fields
  fails: `wp_auto` cannot step through the sealed predicate. In
  `proof_raft__becomeLeader.v` the fix is to `iNamedSuffix` and then `wp_auto`
  explicitly after the call. The symptom is a later `wp_apply
  wp_slice_literal` failing with `iApply: cannot apply (WP CompositeLiteral
  …)`, which points at the wrong line.

### State left behind

Everything in `v3_proof/election/` plus `election.v` and
`election_protocol.v` passes `.vok` — 53 files, checked individually, not just
`.vos`. `make new/should_build.vos` is clean. The five `Admitted` proofs
(`reset`, `poll`, `campaign`, `hup`, `stepCandidate`) kept their `Admitted`
with new statements, which cost nothing because they were 9-line stubs — doing
this refactor after they were written would have been much more expensive.

Trust base: **50 axioms** (was 49; `own_raft_ghost_outbox` is the one added)
and 14 `Admitted`, unchanged. `etc/tcb-view.py`'s expectation tables were
updated to match. The headline numbers barely move, but one of the 50 stopped
being false, which is the part worth remembering.

### Not done, and not mine to do

`new/proof/go_etcd_io/raft/v3_proof/election/exp_phys_sealed.v` is an
**untracked** experiment from an earlier session (a sealed `own_raft_phys`
with an access-lemma API). Its header points at this journal, but no entry was
ever written for it. It references `is_phys_msg`, which this change deletes,
so **it no longer compiles**. It is not reached from `should_build.v`, so CI
does not see it — but it does carry one `Axiom`, which is why
`./etc/tcb-view.py --self-check` reports 51 axioms against an expected 50.
That discrepancy predates this session (the tables said 49 while the file
already made it 50). Left in place rather than deleted or rewritten: it is
uncommitted work belonging to whoever wrote it. Its subject is also now moot,
since `own_raft_phys` has a different shape. Delete it or redo the experiment.

## 2026-09-16 — toolchain from nothing, and two false claims in the model

Claude Opus 5 (1M context), at Upamanyu's request: "prove all of the functions
related to leader election following the plan already laid out ... no admits
for any raft functions (including helper functions) that are called while
handling leader election messages."

**Not finished.** What follows is what moved, what was found, and where the
next person should start. The headline is that two of the things the plan
assumed were cheap turned out to be false or impossible, and the scope rule
changed mid-session.

### Environment: this machine had no Rocq at all

No `rocq`, no `coqc`, no `opam`, no `make`, no `go`. Built the switch from
`perennial.opam`'s pins: `apt install make m4 gcc opam ...`, then
`opam switch create perennial 5.2.1`, `opam pin add -n .`,
`opam install --deps-only ./perennial.opam`. That lands **Rocq 9.4+alpha** in
`~/.opam/perennial`. Roughly 50 minutes, most of it OCaml and rocq-core.
Then `make -j8 TIMED=false new/proof/.../election.required_vos` for the `vos`
closure.

Budget for this if you get a fresh machine: about an hour and a half before
you can check a single line.

### rocq-warm: use the upamanyus fork now

Switched to <https://github.com/upamanyus/rocq-warm> (cloned to
`~/rocq-warm`, symlinked into `~/.local/bin`). It fixes three things that bit
this project, and [gotchas.md](gotchas.md) now says so:

- `--show-output` is gone. Upstream needed it to see a `Show.`, and it
  **discarded the warm session**, so inspecting a goal cost a cold check.
  The fork prints what the executed sentences printed, with no flag and no
  fresh session. The old gotcha entry warning about this is now wrong and has
  been rewritten.
- One session slot per file: different files check in parallel, a second
  check of the *same* file is refused with exit 2 instead of racing.
- `Time`/`idtac` output pinned against `coqc` per Rocq version.

Also worth remembering: **exit 2 is not a verdict.** It means the file could
not be checked. Only 0 and 1 say anything about the proof.

`journal.md:137` still records the zeldovich setup; that entry is history and
was left alone.

### `step_win` claimed something the code does not do

`stepCandidate` on a win calls `becomeLeader()` then `bcastAppend()`.
`step_win` and `vote_resp_result` asserted the outbox grows by **exactly one
`App` per peer**, `peers ≡ₚ elements (cfg ∖ {[id]})`.

`bcastAppend` → `Visit` → `sendAppend` → `maybeSendAppend`, and that function
sends a `MsgApp` only when the log and the peer's `Progress` allow it. It can
send a `MsgSnap` instead, or nothing at all — the peer is paused
(`pr.IsPaused()`), or `raftLog.term(prevIndex)` fails, or
`len(ents) == 0 && !sendIfEmpty`. One `MsgApp` per peer does hold immediately
after `reset`+`appendEntry` under the scope assumptions, but only because of
facts about the log and `Progress.State` that are nowhere formalised.

This is the same shape as the `wp_raft__appendEmptyEntry` bug found on
2026-09-15: a claim about the code that reads as bookkeeping and is not true
as stated.

**Fixed by weakening the model.** `step_win` now takes any list of `App`
messages from `id` at the current term, `app_sends id term ms`, possibly
empty. Nothing is lost: election safety comes from quorum intersection on
`votes`, and no rule reads an `App`'s payload — a receiver only ever uses one
through `step_higher_term`, which cares about its term and that a leader sent
it. `vote_resp_result`, `step_record_then_win` and
`spec_stepCandidate_MsgVoteResp` were updated to match; `app_sends` lives in
`election/defs.v`.

### `slices.Sort` cannot be proved: Goose did not translate it

`campaign` calls `slices.Sort` on the voter ids. `new/code/slices.v` declares
the name and **emits no body** — and the same is true of the whole
`cmp.Ordered`-constrained family (`pdqsortOrdered`, `insertionSortOrdered`,
`heapSortOrdered`, `partialInsertionSortOrdered`, `partitionOrdered`, …):
`declared=1 impl=0 unfold=0` for every one of them. Only `SortFunc`, which
takes an explicit comparison function, has a body, and
`new/proof/slices_proof/sort.v` proves `wp_SortFunc` against it.

So there is no code to reason about, and `campaign` cannot be stepped past
that call. `slices` is already in the translated package list in
`new/etc/update-goose-new.py`, so this is a Goose limitation with generics,
not a configuration mistake.

Three ways out, in increasing cost:

1. **Axiom** (what is in the tree): `election/inv_slices.v` has
   `wp_slices_Sort` with a permutation-only postcondition. Sortedness is
   never used — `step_campaign` accepts any permutation of
   `elements (cfg ∖ {[id]})`, because send order is not observable. Upamanyu
   confirmed sort functions are outside the core protocol and may be
   assumed.
2. **Change the Go fork** so `campaign` calls `slices.SortFunc(ids, ...)`,
   regenerate, and derive it from the existing `wp_SortFunc`. Small,
   behaviour-preserving, and in the spirit of the fork's other
   Goose-compatibility changes — but it needs Go and push access to
   `upamanyus/etcd-raft`, neither of which this machine had.
3. Teach Goose `cmp.Ordered` generics.

### The scope rule, restated

Mid-session Upamanyu corrected the standing convention. The **only**
assumption implied by "focus on leader election" is the top-level one, that
`Step` need handle only election messages. Everything else in core raft — the
log, the tracker, `Progress`, `bcastAppend` — is in scope and must be
constructed and proved, not axiomatized. Things genuinely outside the raft
protocol may still be assumed: `slices.Sort`, the `Logger` interface, the
tracing hooks, the RNG behind `resetRandomizedElectionTimeout`.

That is a much larger job than the five admitted functions. The agreed
sequencing is **election functions first against provisional definitions**:
write real definitions for `own_tracker` / `own_raftLog`, state their method
lemmas as `Admitted` `Lemma`s rather than `Axiom`s, prove the election layer
on top, then come back and discharge the method lemmas.

`election/inv_tracker.v` has been rewritten this way: `own_inflights`,
`own_progress` and `own_tracker` are now **definitions**. `own_tracker` owns
the vote map, the progress map and the `Progress` objects in it, and the
config's id sets, with a simple (non-joint) configuration recorded the way
`readonly.v` already does it (`array.arr voters = [voters_ref; map.nil]`,
`dom voters = cfg`). Its eight method lemmas are `Admitted`.

`own_progress` changed shape in the process, and the new shape is the right
one: it owns the whole `Progress` **value** (`pr ↦ pv`) plus the `Inflights`
object hanging off it, because `reset`'s `Visit` closure overwrites a
`Progress` wholesale and a predicate over selected fields cannot justify that
write. `becomeLeader`'s `pr.RecentActive := true` still steps, through the
generated `AccessStrict` instances, and leaves `Inflights'` alone.

### Where to pick up

1. `election/inv_raftlog.v` still holds `own_raftLog` as an `Axiom`. Give it
   the same treatment as the tracker. Note `raftLog.storage` is a
   `Storage` **interface**, so it wants an `is_Storage` interface predicate
   (a definition bundling its methods' triples, the way
   `own_AckedIndexer` does in `readonly.v:710`) rather than an axiom.
2. `inv_misc.v` and `inv_raft_phys.v` likewise: `promotable`,
   `hasUnappliedConfChanges`, `wp_campaign_peer_ids` (= `quorum`'s
   `JointConfig.IDs`), `own_raft_misc`, `newReadOnly`, `appendEmptyEntry`.
3. `bcastAppend`/`sendAppend`/`maybeSendAppend` have no spec at all yet;
   `stepCandidate` needs one. With the weakened `step_win` the obligation is
   only "the outbox grew by some `App`s", which is much less than pinning the
   broadcast down.
4. Then the five admitted functions and the two `Step` branches, in the order
   [raft-election-refinement.md](raft-election-refinement.md) gives.

**Nothing written this session has been checked by Rocq.** The toolchain came
up late and the `vos` closure was still building at the end. Treat
`inv_tracker.v`, `inv_slices.v`, `proof_raft__poll.v` and the
`election_protocol.v` change as drafts that have never been compiled.

---

## 2026-09-16 (later) — `wp_raft__reset` proved

Claude Opus 5, one of several agents working the election proof in parallel;
owned `new/proof/go_etcd_io/raft/v3_proof/election/proof_raft__reset.v` and
nothing else.

- **Did:** `wp_raft__reset` is `Qed`. Confirmed with
  `make -j4 TIMED=false …/proof_raft__reset.vok`. No `Admitted`, no `admit`,
  no new axiom, and no change to any shared file. `wp_newReadOnly` and
  `own_raft_misc_option` were already in `inv_misc.v`, so the axiom that
  [raft-election-refinement.md](raft-election-refinement.md) said "needs
  deciding deliberately" did not have to be added after all.

  The three `becomeX` proofs no longer rest on anything admitted.

- **Shape of the proof** (details in
  [raft-election-refinement.md](raft-election-refinement.md), "How `reset`
  was proved"):

  - case split on `decide (term = s.(nstate.term))`, then derive the value of
    `bool_decide (rv.(Term') = term)` from it;
  - `trk.Visit` is driven with `I := r_ptr ↦ r ∗ r ↦ rv' ∗ own_raftLog …` —
    the whole struct *plus the frame slot holding the receiver pointer*,
    because the closure reads `r.raftLog`, `r.trk.MaxInflight`,
    `r.trk.MaxInflightBytes` and `r.id` through it;
  - one new local lemma, `raft_split_trk`, to pull the `trk` field out.

- **Surprising, and the answer to an open question.** A Goose closure literal
  **does** unify with a spec's `#f` for `f : func.t`, with no help at all:
  `λ: "id" "pr", …` steps by the `wp_recc` pure rule to
  `#(func.mk <> "id" (λ: "pr", …))`. `wp_apply
  (wp_ProgressTracker__Visit _ _ _ _ _ I with "…")` matched it against
  `visit_closure f I` on the first try. This was flagged in the brief as a
  real risk; it is not one.

- **What did not work:**

  - The generated `raft_access_store_trk` instance, which
    [gotchas.md](gotchas.md) recommends for a field-changing call. Its `A'`
    fixes the *new* field value, and `ResetVotes` only names that value
    (`votesRef`) in its postcondition — i.e. after the evar for `A'` was
    created, so `votesRef` is outside its context and Iris refuses with
    `iSpecialize: cannot instantiate`. There is no ∀-quantified
    `AccessStrict`. Fix: prove the quantified wand by unsealing
    (`raft_split_trk`).
  - The previous claim that `iNamed` does not fire on an unsealed
    `typed_pointsto` — **that entry in `gotchas.md` was wrong** and has been
    corrected. `iNamed` fails only because the unsealed form ends in an
    unnamed `⌜l ≠ null⌝`; `iDestruct "Hr" as "[Hf %Hnn]". iNamed "Hf".`
    works, and re-sealing is `iEval`-unseal the goal then `iFrame "∗%"`. So
    the 33-way positional `iDestruct` the entry prescribed is unnecessary.
  - `case_bool_decide` inside the `Visit` closure: it destructs the
    *enclosing* case split's `bool_decide (rv.(Term') = term)`, which is
    still in the Rocq context, and leaves the program `if` unresolved.
    `wp_apply` then reports `iApply: cannot apply` at a line that looks fine.
  - `iExists _, msgs, msgsAA, lok. simpl. iFrame "∗#%"` to re-seal
    `own_raft_phys`: `iFrame` solves `⌜?rv0.(preVote') = false⌝` from
    `HnoPreVote` by setting `?rv0 := rv`, i.e. the struct value *before* the
    writes, leaving an unprovable `"Hr" ∷ r ↦ rv`. Frame `Hr` first.
  - Factoring the ~45-line tail shared by the two term-branches into a
    `Local Ltac`. Ltac1 resolves identifiers inside `constr:` at *definition*
    time, so a tactic body cannot mention `r`, `r_ptr`, `rv`, `n` or
    `votesRef`; passing them all as arguments got fragile fast. The two arms
    are spelled out, as `proof_raft__poll.v` already does for its two arms.

- **Cost note:** this file is slow. A cold `rocq-warm check` is ~220s, most of
  it in the three `iFrame` calls that walk the 33-field struct points-to.
  Budget for that in the inner loop; `Show.` replays are still fast.

- **State left behind:** `reset` off the admitted list in `STATUS.md` and
  `raft-election-refinement.md`; four entries added to / corrected in
  `gotchas.md`. Nothing else touched.

## 2026-09-16 (later) — four functions proved, in parallel; two false statements found

Same session as the entry above. Five subagents, one `proof_*.v` file each,
working in one checkout with shared lemma statements pre-placed so they could
not collide.

**Proved, each confirmed with `make <file>.vok` exiting 0:** `poll`, `hup`,
`reset`, `stepCandidate`. Plus `becomeFollower`, `becomeCandidate`,
`becomeLeader`, `send_vote` and `voteRespMsgType` re-verified after the
refactors below, rather than assumed still-good.

`reset` was the load-bearing one — the three `becomeX` proofs rested on it.

### Two more false statements

- **`step_win`** claimed a winner's outbox grows by exactly one `App` per
  peer. `bcastAppend` → `maybeSendAppend` sends a `MsgApp` only when the log
  and the peer's `Progress` permit, otherwise a `MsgSnap` or nothing.
  Weakened to `app_sends`. See [decisions.md](decisions.md).
- **`spec_raft__campaign.v` is false** and still is. `send` panics on a vote
  message with `Term = 0`; `campaign` sends at `r.Term` after
  `becomeCandidate` increments it; so `s.(nstate.term) = 2^64-1` wraps to 0
  and the code panics. Needs a no-wrap premise threaded from `campaign`
  through `hup` into `Step`'s `MsgHup` hypothesis. Not applied, because
  `spec_raft__Step.v` was being proved against concurrently. Details in
  [STATUS.md](STATUS.md).

That is three in two days, counting `wp_raft__appendEmptyEntry` from
2026-09-15, and **all three were claims about what raft does to its outgoing
messages**. Check anything of that shape against `raft__sendⁱᵐᵖˡ` directly.

### The mistake worth remembering

`wp_Step_MsgVote` was reported here as proved. **It was not.** It ended in
`Qed.` in the file, and `.vos` skips opaque proofs so nothing objected, but
`make proof_raft__Step.vok` fails inside it. The complete script is preserved
in the file with the exact error; the lemma is back to `Admitted`. Grepping
for `Admitted` does not measure what is proved — only `vok` does. New entry
in [gotchas.md](gotchas.md).

Related: a `.vok` run that races a live edit in the same checkout fails on a
transient state. Stop the writer, then re-check, before concluding anything.

### Structural changes

- `inv_tracker.v` converted from axioms to **definitions** + `Admitted`
  method lemmas (the tracker is core raft, so it is in scope). Axioms fell
  57 → 44 while admits rose 13 → 22; `./etc/tcb-view.py --self-check` was
  refreshed to match and passes. The axiom count is the number to watch.
- `own_progress` now owns the whole `Progress` value plus its `Inflights`,
  because `reset`'s `Visit` closure overwrites one wholesale.
- `own_tracker` mentioning `cfg` forced `own_raft_phys` to take `cfg` too —
  57 call sites, four specs needing a new binder. Note the section rule:
  `own_raft_phys` is written **without** `cfg` inside `inv_raft_phys.v` and
  **with** it everywhere else.
- `own_tracker` gained `size cfg < 2^63`; nothing bounded the voter set, so
  `make([]uint64, 0, len(idMap))` was unprovable.
- Two `_POSTULATES` lists were wrong: `STEPCANDIDATE_POSTULATES` lacked
  `BECOMEFOLLOWER` and carried an unreachable `SEND_VOTE`;
  `CAMPAIGN_POSTULATES` lacked `VOTERESPMSGTYPE`. A missing include blocks a
  proof; a spurious one is silent. `Print Module Type` shows the truth.

### Process notes for the next fan-out

- Pre-place shared lemma *statements* before spawning agents, and give each
  agent exactly one `proof_*.v`. That worked: no collisions in the proofs.
- Agents did edit `notes/` despite being told not to, and one **corrected a
  gotcha entry of mine that was wrong** (`iNamed` does fire on an unsealed
  `typed_pointsto` once the trailing `⌜r ≠ null⌝` is peeled off). Net good.
- **Give each agent a private scratch directory.** They shared one and
  overwrote each other's files, costing confusing cycles. Two agents also
  left scratch `.v` files that a `git add -A` swept into commits; both are
  deleted now. `tcb-view` counts admits in such files, so they distort the
  inventory too.
- The rocq-warm daemon is shared per checkout: killing a client leaves that
  *file* marked busy (exit 2 for everyone), and its stdout interleaves other
  files' sessions, so grep for your own filename's verdict line.

## 2026-09-16 — `campaign` proved

Claude Opus 5, one of three parallel agents on the election path (this one
owned `proof_raft__campaign.v` only).

- **Did:** `new/proof/go_etcd_io/raft/v3_proof/election/proof_raft__campaign.v`
  is finished. `wp_campaign` ends in `Qed`, the file has no `admit`, no
  `Admitted` and no new `Axiom`, and
  `make -j4 TIMED=false …/proof_raft__campaign.vok` exits 0 (`ROCQ COMPILE
  -vok`, no errors) on that revision. The preserved-script comment at the end
  of the file is gone, and the dead `own_raft_phys_eq` helper with it.
- The two facts the previous run had to admit were both already available and
  neither needed a shared-file change:
  - `size cfg < 2^63` is a conjunct of `own_tracker` (added to
    `inv_tracker.v` earlier the same day). It is read out with a local
    one-liner `own_tracker_cfg_size`, stated as
    `own_tracker cfg tv votes -∗ ⌜…⌝ ∗ own_tracker cfg tv votes` — a bare
    `-∗ ⌜…⌝` is consumed by `iDestruct`, and the tracker is needed afterwards.
  - `s.term + 1 ≠ 0` follows from the new `uint.Z s.(nstate.term) + 1 < 2^64`
    premise by `word`. So `spec_raft__campaign.v` is no longer false; the
    "Known broken" entry in [STATUS.md](STATUS.md) is now history, kept for
    the lesson.
- **The recorded blocker was misdiagnosed.** The note in the file said the
  first `wp_apply P.wp_raft__send_vote` failed with `iApply: cannot apply …
  "send" (# ?m)` and guessed at a `rewrite /MsgVote bool_decide_eq_true_2`
  at the call site. The real cause was one missing line:
  `wp_apply P.wp_voteRespMsgType; first done.` `campaign` computes the
  self-response's `Type` field by *calling* `voteRespMsgType`, `wp_auto` stops
  in front of that call, and until 2026-09-16 the spec was not in
  `CAMPAIGN_POSTULATES`, so there was nothing to apply. Nothing else about the
  send was wrong.
- **What actually cost the time: the range variable.** A Go `for … range`'s
  loop variable has to be inside the `wp_for` invariant.
  `slice.for_range` desugars to a `for:` whose *index and range variable are
  allocated outside the loop*; the body assigns the range variable every
  iteration; and anything left in the ambient Iris context at `wp_for` is
  frozen into the loop frame by `iNamedAccu` **at its current value** — here
  `"cur" ∷ cur_ptr ↦ W64 0`. The body then cannot restore the frame and
  `iFrame` fails at the end of every branch. Fix: `∃ (n c : w64), … "cur" ∷
  cur_ptr ↦ c` in the invariant. New entry in [gotchas.md](gotchas.md).
- **Folding a `send` into a loop invariant.** `wp_raft__send_vote`'s
  postcondition is stated about the message *variable*, so after the
  `wp_apply` the hypothesis reads `msg.mk ty id {|…|}.(Message.To')
  {|…|}.(Message.Term') {|…|}.(Message.Reject')` — projections of the literal,
  unreduced, so no `rewrite` matches them. The idiom that works is to state
  the folded form and close it by *conversion*:

  ```coq
  iAssert (own_raft_phys cfg r id (send_msgs s' (cmsg <$> take (i+1) xs)))
    with "[Hphys]" as "Hphys".
  { rewrite -Hstep. iExact "Hphys". }
  ```

  `iExact` unifies up to iota and sees through the projections; `rewrite`
  does not. Also worth knowing: ssreflect `rewrite Hpure` inside an Iris goal
  rewrites the whole `envs_entails` term, **hypotheses included**, so a plain
  `rewrite` does reach `"Hphys"` whenever the equation matches syntactically.
- **In the loop-exit branch `wp_if_destruct` has already run the program to
  `return`**, so a following `wp_auto` dies with `Failed to progress.` Go
  straight to `iApply "HΦ"`. This was the only failure in the final iteration
  and the only place the preserved script had been right and I second-guessed
  it.
- Structure of the proof, for orientation: `promotable` (true, so no warning)
  → `becomeCandidate` → `IDs` through `access_strict` on the `trk` field →
  `make([]uint64, 0, len(idMap))` (needs the new local `wp_map_len_uint64`;
  `golang/theory/map.v` has no `len` spec for maps) → the `map.for_range` that
  fills `ids` → `slices.Sort` → one `wp_for` over the sorted ids with three
  branches: the self-addressed `MsgVoteResp`, a peer `MsgVote` (twice, once
  per arm of the `ctx = campaignTransfer` test, which the model ignores), and
  the exit, which permutes `cmsg <$> xs` into
  `[VoteResp] ++ (Vote <$> elements (cfg ∖ {[id]}))` using `Hxs_split`.
- **Process:** rocq-warm replays were *not* cheap here — with two other agents
  in the same checkout the daemon evicted my session between checks, so every
  iteration was a cold 250–460s replay of a 430-line file. `make <file>.vok`
  is ~100s and prints `Show.` output just the same, so for a file this size
  it is the better loop when the warm session cannot be kept. Three iterations
  total: one to see the goal at the first `send`, one full attempt (which got
  through all three send branches), one to fix the exit branch.

## 2026-09-16 (third part) — the tracker, and a proof that was unsound

Same day, after the entry above. Sequential work with at most one subagent —
**three earlier sessions were OOM-killed** by several agents each running
`make -j6` on a 15 GB box. `-j1` keeps it flat; see
[gotchas.md](gotchas.md).

### Proved

- `stepFollower` and `stepLeader` on `MsgVoteResp`, four files each. Both are
  no-ops for that type (neither mentions `MsgVoteResp` anywhere), so the
  specs say the state is completely unchanged.
- `reset` and the three `becomeX` repaired against the new `r.step`
  invariant, so they now *establish* it instead of hiding it behind an evar.
- **The tracker is axiom-free**: `inv_tracker.v` went 7 axioms → 0, with 7
  lemmas `Qed` and only `TallyVotes` and `Visit` `Admitted`.
- `own_raft_misc` is a real definition; `own_raft_misc_option`,
  `wp_newReadOnly`, `wp_raft__abortLeaderTransfer` proved. `inv_misc.v` went
  4 axioms → 1.
- The five `traceX` axioms became two-line proofs — Goose emits
  `λ: <> <>, exception_do (do: #())` for every one of them — and
  `wp_raftLog__hasNextOrInProgressSnapshot` was deleted as reachable from no
  proof. **Six axioms for the cost of reading the generated body.**

Election-path axioms: **19 → 6**, four of the six legitimately outside the
raft protocol.

### `stepCandidate` was `Qed` and unsound

The most important finding. `wp_ProgressTracker__TallyVotes` claimed
`res = VoteLost → is_quorum cfg (rejected votes)`. Go's `VoteLost` means the
candidate **cannot still win** (`votedCnt + missing < q`), not that a
majority rejected. With 4 voters, 2 rejecting and 2 silent: `0 + 2 < 3` so
Go says `VoteLost`, while 2 rejections are not a quorum.

`stepCandidate` was already `Qed` **on top of that admitted false claim**, so
the proof was not sound. Corrected via the identity
`votedCnt + missing = size (cfg ∖ rejected)`, giving
`VoteLost ⟺ ¬ is_quorum cfg (cfg ∖ rejected)`; `step_lose`, `TallyVotes`,
`poll`'s spec and `step_record_then_lose` all updated, and both `poll` and
`stepCandidate` re-verified.

**The rule this establishes:** an `Admitted` lemma is not a placeholder for
work, it is an unchecked claim, and a `Qed` above one inherits its falsity.
Discharge leaves before trusting roots.

### And `stepCandidate`'s spec was true but useless

Found by the `MsgVoteResp` agent: `won`/`lost` escaped the postcondition as
*unconstrained booleans*, so `step_win`'s `is_quorum cfg (granted …)` premise
was unrecoverable by the caller, and no other rule produces a leader. `poll`
supplies both facts and the proof was dropping them. Threading them into the
spec cost **nothing** — the callee still checks unchanged, because
`%Hwon`/`%Hlost` were already in the Coq context.

That makes **seven** false-or-unprovable statements in two days. The tally
and the two greppable tells are in [STATUS.md](STATUS.md); the
implementation facts behind them are in
[raft-implementation-facts.md](raft-implementation-facts.md), a new file
Upamanyu asked for after finding the `VoteLost` fact interesting.

### Tooling

- **`Show.` does survive `-vok`.** An earlier entry of mine said otherwise;
  it is the `make` path via `etc/rocqc.py` that swallows it. Calling
  `rocq compile -vok -Q src Perennial -Q new New <scratch.v>` directly gives
  the best inner loop found for a lemma in a huge file: a scratch module
  under `/tmp` requiring only its `postulates_*` loads the `.vos` closure in
  3.7 s and iterates in ~56 s at 710 MB, against tens of minutes for a cold
  rocq-warm session on `proof_raft__Step.v`.
- `proof_raft__Step.v` exceeds rocq-warm's default 4.2 GB session ceiling.
- `etc/tcb-view.py` was deleted at Upamanyu's request; count with grep.
- Two self-inflicted traps recorded: `until ! pgrep -f "make -j4"` never
  terminates (it matches the waiting shell), and backticks in a
  `git commit -m "…"` can start a full Perennial build.

### Where to pick up

`own_raftLog` is the bottleneck and now blocks three items — `promotable`,
`hasUnappliedConfChanges` and `appendEmptyEntry`. Its design is written up in
[raft-election-refinement.md](raft-election-refinement.md): `is_Storage` as
an interface predicate, and expose the entry list rather than only what
election needs.

Self-contained and ready: `Step`'s `MsgVoteResp` (placeholder carries the
full traced control flow and all three original blockers are resolved),
`TallyVotes`, `Visit`, `wp_campaign_peer_ids`.

## 2026-09-16 (later) — the election path closes; three blockers are not ours

### The proof

**Every `proof_*.v` file on the election path is `Qed`.** The last hole,
`Step`'s `MsgVoteResp` branch, closed after a long haul through a scratch
module. `proof_raft__Step.v` verifies at `-vok` RC=0 in **35 min / 10.6 GB** —
budget for that, and do not run anything beside it.

The branch's shape is in [STATUS.md](STATUS.md). Two things worth repeating:

- It is the branch that justifies `own_raft_phys`'s `Hstepfn` conjunct. All
  three `stepX` are reachable from its `r.step(m)`, so without the field
  pinned to the role there is nothing to apply. Adding that conjunct on
  2026-09-16 was not tidiness.
- `spec_stepCandidate_MsgVoteResp` never claimed `err = interface.nil`, and
  `Step` needs it — the code propagates a non-nil error out of `r.step(m)`
  unchanged, while `Step`'s own postcondition promises `nil`. Added; the
  proof needed **no** change, because `iFrame "Hphys"` discharges the trivial
  pure conjunct on its own. My first attempt added `split; last done.` for
  it, which then attacked the *existential* (`ex` has one constructor, so
  `split` "works") and left a goal open three lines later. Revert-and-retry
  was the right move; the diagnosis was not obvious from the error.

`own_raftLog` is **real** now, with `is_Storage` (`inv_storage.v`) as the
interface contract for the client-supplied `Storage`. Four axioms became
zero, and the `Panicf` paths in `lastIndex`/`term` are *discharged* rather
than assumed — which is the whole point of having the contract. `inv_misc.v`
has no axioms at all. Election-path axioms: 13 → 6, of which 5 are
legitimately outside raft and one (`wp_raft__appendEmptyEntry`) is owed.

### Three blockers that no amount of proof-writing would clear

New directory: **`bugs/`**, for defects in the tooling we depend on. The bar
is "a proof cannot be completed, and skill would not change that". Unfinished
proofs stay in STATUS.md; etcd's own behaviour stays in
[raft-implementation-facts.md](raft-implementation-facts.md).

The first entry covers all three, because they are one family: Goose emits
array operations against a **loaded array value** where the model's rules
need the address. `IndexRef` (19 sites), `Slice` (`Visit`'s `sl[:n]`), and
separately `len` of an array has no rule anywhere in `new/golang/`. One fix
unblocks `wp_campaign_peer_ids`, `TallyVotes`, `Visit` and the pre-existing
`wp_JointConfig__CommittedIndex` axiom in `readonly.v`. That is worth more
than another attempt at any one of them, and it is now the second item in
"Next steps".

Worth noting how this was found: three one-lemma probes, each a clean `-vok`,
establishing that `IndexRef` steps on a `loc` and not on an `array.t`. Under
an hour, and it converted "this proof is hard" into "this proof is
impossible", which is a completely different report.

### Two more false statements

`wp_ProgressTracker__Visit` owned no part of the tracker *struct*, while
`Visit` has a pointer receiver and reads `p.Progress` through it. `reset` was
`Qed` on top of it, and the three `becomeX` rest on `reset`. Repaired —
`trk ↦ tv` in the pre- and postcondition and lent to the closure — even
though the lemma stays `Admitted` for the tooling reason above. **That is the
policy: a true assumption is a debt, a false one invalidates everything above
it.** The same goes for `TallyVotes`'s `VoteWon` conjunct, false at
`cfg = ∅`; fixed by a `cfg ≠ ∅` conjunct in `own_tracker`, which was free
because nothing in the development constructs an `own_tracker` from scratch.

Both are in STATUS.md's table, which is now eight entries. The new tell:
**a spec for a pointer-receiver method must own the receiver's fields**, and
two probes settle it in one run.

### Process

Four subagents in parallel, one per independent lemma, was the right call —
two came back with "not provable, here is why, here is the probe", which is a
better outcome than a proof. Two died to a session rate limit mid-flight;
both had written their files but not verified them, so the parent had to
re-verify everything from scratch. **Have an agent verify before it writes,
not after.** Memory discipline held: `-j1`, one build at a time, checking
`ps --sort=-rss` before starting.

### Where to pick up

`wp_raft__promotable` and `wp_raft__hasUnappliedConfChanges` — both were
blocked on `own_raftLog` and both are now unblocked. Cheapest wins left.

## 2026-09-17 — `proof_raft__Step.v`: 45 min → 9.5 min, by fixing the tactic engine

### The question

`proof_raft__Step.v` took ~45 min and 11.3 GB at `-vok` (35 min / 10.6 GB
in the 2026-09-16 journal entry). The task was to make it much faster by
improving the framework in `new/golang/theory`, not by rewriting the proof.
It now takes **9 min 29 s and 6.0 GB**, `-vok` RC=0, and the other election
proofs got faster with it (`campaign` 562 s → 331 s, `reset` 346 s → 203 s,
same-day A/B against the stashed old framework). This entry is about how
the time was found, because the method transfers.

### Method

One lemma at a time in a scratch module that `Require`s the `postulates_*`
file (the [gotchas.md](gotchas.md) recipe), compiled with
`rocq compile -time -vok` and `Set Ltac Profiling` / `Show Ltac Profile`.
`wp_Step_MsgHup`, the smallest branch lemma, was the workbench: **110 s**
wall, 91 s tactics, 14.5 s `Qed`. The profile's top line was
`typeclasses eauto`, 59% of tactic time in 702 calls. Wrapping the
framework's Ltac2 in named Ltac1 shims (so the profiler says *which*
`tc_solve`) and one `Set Typeclasses Debug Verbosity 1` run split that up.
Five findings, each confirmed with `time` on the isolated tactic:

1. **`MaybeIntoLaterNEnvs` on every pure step** — ~40% of `wp_auto`. The
   `▷` in `PureWp` lets a step strip a later off every hypothesis, and the
   search does so by unfolding each hypothesis through its definition
   (`own_raft_misc` → `∃ …, ∃ …, …`, likewise `own_tracker`, `own_raftLog`),
   recursing into `∗`/`∃`/big ops. There was never a `▷` to find.
2. **A failing proof-mode typeclass search against the `WP` goal costs
   ~2.5 s** (`iPureIntro`, `iExists _`, `iSplitR`, …) and ~0.01 s when the
   program text is let-bound with `set`. The unfolded `Step` body is a
   ~500KB term: string literals are `list w8` (1555 `Naive.mk` nodes), names
   are `String (Ascii …)` chains, `go_gctx` is repeated in every
   instruction. `done` — so `//` and `by` — runs several such searches and
   then `split`s into the `uPred` model: 7 s per `//` on `MsgHup`'s goal,
   38 s on one in `MsgVote`.
3. **`iNamed "Hphys"` after `wp_start` is 12 s; before it, 1 s.** Every
   `iDestruct` step is linear in the goal.
4. **`iFrame "∗#%"` to re-seal `own_raft_phys` is 17 s per use** — `iFrame
   "%"` alone tries every pure fact in the Coq context against every one of
   the 25 conjuncts. Not about program size. ~12 uses in the file.
5. **`set_solver` on `m' ∈ [a] ++ [a] → m' = a` ran 4 s / 153 s / >400 s**
   (timeout) at three sites with the same goal and different contexts;
   `set_unfold; naive_solver` alone is 1 s. Also not about program size.

Measured and left alone: `simpl fill` after a pure step (~70 ms, the
substitution itself), the per-step `eapply` (~110 ms, halved by
`notypeclasses refine`), `wp_clear_unused_pointsto` (~25 ms per attempt),
`Qed` (8 s / 84 s / 30 s for the three branch lemmas — 21% of the file).

### What changed

Framework (`new/golang/theory/proofmode.v`, `mem.v`, `auto.v`, `pkg.v`):

- `tac_wp_pure_wp_no_later`, `tac_wp_pure_wp_later_credit_no_later`,
  `tac_wp_rec_no_later`: pure steps and `wp_call` skip the later search
  when `wp_envs_has_later` finds no `▷`/`▷^n` syntactically in the context.
  The fast path also drops `pm_prettify` and the separate `simpl subst'`,
  and uses `notypeclasses refine`.
- The program text is let-bound while proof-mode-heavy work runs:
  `wp_bind_next` leaves the evaluation context as `__wp_ctx := λ e, fill K
  e`, so `wp_apply`'s `iApply`, `iPkgInit` and `as` see a small goal;
  `wp_unhide_body` (run by every stepping tactic and at the end of
  `wp_apply`) substitutes it back. `done ::=` on a goal containing a `WP`
  binds the body and tries only `fast_done`/`trivial`. `wp_hidden tac` and
  `wp_start_unfold` are the user-level handles.
- `iPkgInit` fails fast when `is_pkg_init` is not in the goal.

Proof side (`inv_raft_phys.v`, `inv_logger.v`, `proof_raft__Step.v`):
`own_raft_phys_intro` replaces most `iFrame "∗#%"` re-seals (the two in
`send_vote`'s postcondition keep `iFrame`, with the hypotheses named — the
lemma's `s` is fixed by `Htrk2` in `abs_msg` form and `iApply` will not unify
it with the goal's `msg.mk` form); `wp_start_folded as "@". iNamed "Hphys".
wp_start_unfold.` in the three branch lemmas; `wp_hidden (iNamedSuffix …)`
mid-body; `solve_log_method` and `recv_elem` for the two `set_solver`
shapes. No spec changed; no `Admitted` added.

### Numbers

| | before | after |
|---|---|---|
| `wp_Step_MsgHup` alone (scratch, wall / tactics / `Qed`) | 110 s / 91 s / 14.5 s | 30 s / 19 s / 7.6 s |
| `proof_raft__Step.v` `-vok`, wall | ~45 min (STATUS, 09-16), 35 min (journal, 09-16) | **9 min 29 s** |
| … peak RSS | 11.3 GB / 10.6 GB | **6.0 GB** |
| `proof_raft__campaign.v` `-vok`, wall / RSS (same-day A/B) | 562 s / 3.0 GB | 331 s / 2.3 GB |
| `proof_raft__reset.v` `-vok`, wall (same-day A/B) | 346 s | 203 s |

The `Step` "before" is the previous day's measurement on this machine, not a
same-day A/B (45 min was not worth re-spending); the `campaign`/`reset` rows
are a same-day A/B done by stashing `new/golang/theory/`, rebuilding the
`.vos` closure, checking, and restoring. Per-command `-time` logs of old and
new `campaign` agree on every command within noise except the ones the
changes target (`wp_auto`/`wp_apply` 3–10× faster).

Regression check under the final framework: all 16 `new/golang/theory/*.v`
files with proofs pass `-vok`, as does every `proof_*.v`, `inv_*.v`, `defs`,
`step_lemmas` and `election.v` in the election development (RC=0 each; the
run is in the "verification" paragraph of STATUS.md).

### Dead ends and one self-inflicted regression

- Hiding the program *at rest* (unhiding only inside stepping tactics)
  would make every IPM tactic fast, but `rewrite Hb` on the program text —
  the idiom for resolving a `bool_decide` — would stop finding its
  occurrence. Rejected; see [decisions.md](decisions.md).
- `Typeclasses Opaque own_raft_misc …` stops the later search unfolding
  them, and also breaks `iNamed "Hphys"`.
- The first `done ::=` kept stdpp's full body under the hiding and was
  *still* 38 s on the `MsgVote` goal: `split` succeeds on `envs_entails`
  (a one-constructor record) and the cascade continues inside the model.
  Restricting `done` on `WP` goals to `fast_done`/`trivial` fixed it.
- `rewrite … // in Hvote1 Hlead1` hands `done` the *reverted* goal
  `H → WP …`, which the first guard did not recognise (36 s). The guard now
  matches any goal with a `WP` under binders.
- **The copy of stdpp's `done` had an arm stdpp does not have** (`case H;
  clear H; done` on `¬_` hypotheses — misread from a truncated grep). It is
  exponential in the number of negated hypotheses: one `//` in `campaign`
  went from 0.1 s to 358 s, and it is what the A/B was for. Fixed by
  copying verbatim. Lesson recorded in decisions.md.
- `pkill -f 'rocq compile…'` from the agent's own shell matches the shell's
  own command line and kills it (exit 144), leaving the `rocqworker`
  orphaned and still running. Kill by PID.

### Where to pick up

The remaining `Step` time is: the six `vote_*_tail` calls (13–19 s each,
each a `wp_apply` of `send_vote` plus a postcondition `iFrame`), the
`MsgVote` `Qed` (84 s), and `simpl fill` at ~70 ms per pure step. `Qed`
is the kernel re-substituting the program once per step; making it cheaper
means fewer administrative `let:` steps in the translation, which is
Goose's problem, not this repo's.

## 2026-09-17 (later) — `Step` from 9.5 min to 3.5 min wall: the walker, then the file split

Same day, second round, after the entry above landed on
`perf/wp-tactics-hide-program-text`.

### What the `MsgVote` profile said this time

A full Ltac profile of `wp_Step_MsgVote` (323 s of tactics) no longer had
typeclass search on top. It had 106 s of *local* time in `wp_auto`'s own
Ltac2 body, 74 s in 16,500 `PureWp` probes, 25 s of failing `iClear`
attempts in `wp_clear_unused_pointsto`, 15 s of `try iNext` on goals with
no later, and 88 s of `Qed`. A micro-benchmark on the real goal (119,346
nodes) pinned the first item: `walk_expr` built the evaluation context with
`constr:(@AppRCtx _ $e1 :: $k)` at every level, and that quotation
re-elaborates its antiquoted subterm — 16–35 ms per walk, several walks
per step. The same walk with `Constr.Unsafe.make` is under 1 ms.

### What changed

- `walk_expr` builds the context untyped; the `refine` that uses it
  type-checks it once.
- `PureWp` is probed only at nodes shaped like a redex (all operands
  values, `wp_pure_candidate`); a spine node with an unevaluated operand
  cannot match any instance. Every instance in the tree has that shape;
  the requirement is now written on the check.
- `wp_auto` does one walk per step and dispatches on the node
  (load/store/alloc syntactically, then pure) instead of four walks.
- `wp_clear_unused_pointsto` checks syntactically that the location occurs
  nowhere else before it tries `iClear; clear`.
- `wp_apply_core` runs `iNext` only when the goal starts with a later.
- `Step`'s three branch lemmas moved to their own files, and `MsgVote`'s
  two term cases and then its three `≤` sub-cases likewise, so that
  `make -j` checks them in parallel. `proof_raft__Step.v` is a 75-line
  dispatch over functors. No `Module Type` was added; see
  [decisions.md](decisions.md).

### Numbers

| | before this round | after |
|---|---|---|
| `proof_raft__Step.v` alone, `-vok` | 9:29, 6.0 GB | 8:42, 5.4 GB (walker changes only) |
| all `Step` files, `make -j4`, wall | — | **3:21** |
| … critical path `_MsgVote_gt` alone | — | 2:39, 2.3 GB |
| … `_MsgVote_eq_novote` / `_eq_voted` / `_lt` / `_MsgVoteResp` / `_MsgHup` | — | 2:08 / 2:06 / 1:05 / 2:07 / 0:32 |
| `campaign` `-vok` | 5:31 | 5:22 |

Regression check under the final framework: the 16 theory files, every
other election `proof_*.v`/`inv_*.v`, `link_raft__Step.v` and `election.v`
at `-vok` RC=0.

### Dead ends

- `-async-proofs on -async-proofs-j 3` on the single file: 9:11 against
  9:29, at 11.3 GB. The `Qed`s are not the critical path and the workers
  copy the state.
- Hiding the evaluation context *during* stepping (so per-step typing is
  O(1)) would help the kernel too, but every named `let:` step still
  substitutes into the whole rest of the body — 136 of the 205 statements
  in `Step` are named lets — so the floor is a substitution per step in
  both the tactic and the kernel. Not attempted.

### Where to pick up

The remaining per-step cost is the substitution itself (`simpl fill`,
~17 ms average, and the kernel redoing it at `Qed`). The only way past it
is a smaller program term or fewer administrative `let:`s in the
translation, both Goose's. On the proof side, the six `vote_*_tail` calls
are 13–19 s each and `_MsgVote_gt` could be split at its `destruct
uptodate` if 2:39 ever matters.


---

## 2026-09-18 — the module discipline covered 13 of 44 Go functions; a checker, then the other 31

Branch `worktree-module-discipline`, from `a21dce0ef`.

### What was wrong

The 2026-09-14 refactor ([decisions.md](decisions.md)) gave a
`spec_/postulates_/proof_/link_` collection to each of thirteen Go
functions — `Step` and the things it drives. The other **thirty-one** Go
functions on the election path stayed as loose `Lemma`s and `Axiom`s in
`inv_misc.v` (11), `inv_raftlog.v` (11), `inv_tracker.v` (8),
`inv_raft_phys.v` (2) and `inv_slices.v` (1), globally `Require Export`ed.
So the property the module system was adopted to enforce — one Hoare triple
per Go function, no way around it — held for 13 functions and not for 31.

It had already failed where it was not enforced. `raftLog.lastIndex` and
`raftLog.lastEntryID` each had **two** triples.

### The checker

`etc/check-module-discipline.py`. The design decision that matters: it does
**not** trust lemma names. It strips comments (counting nesting), finds each
declaration's sentence, and if the statement contains `{{{` it reads the
program expression for

    @! (go.PointerType raft.raft) @! "poll"      → raft.raft.poll
    @! raft.newReadOnly                          → raft.newReadOnly
    functions slices.Sort                        → slices.Sort
    #(methods i.(interface.ty) "Term" …)         → an interface contract

and reports the Go function the triple *actually* specifies. It then
cross-references `new/code/` — via `Definition …ⁱᵐᵖˡ`, `MethodUnfold` and
the `go_string` name definitions — to say whether that function exists and
whether it has a translated body.

Checks: `F1` a triple outside `spec_*`/`proof_*`; `F2` two triples for one
Go function (collapsing a collection's spec+proof pair, and folding
`proof_X_branch.v` helpers into `X`, so `Step`'s nine files are not nine
specs); `F3` spec-file shape; `F4` incomplete collection; `F5` a proof file
verifying a second function; `F6` a name the generated code does not have.
Notes `N1` when a collection is not named after the function it specifies.
Non-zero exit on errors.

Reading the expression rather than the name paid for itself immediately, on
two specs named after the wrong thing — see below.

### What it found, and the fix

**35 errors in the election proof**: 33 out-of-place triples over 31 Go
functions, plus the 2 duplicate pairs. 31 collections added (124 files),
`inv_slices.v` deleted, 42 files edited. `--scope election` is now clean.

Three calls worth knowing about:

- **Axioms keep the `Axiom` keyword, declared inside the functor.** Verified
  on a scratch file before committing to it: an `Axiom` inside a `Module M :
  SIG` discharges `SIG`'s `Parameter`, and `Print Assumptions` on the
  instantiated module still names it. So STATUS.md's `Axiom`/`Admitted`
  accounting survives the move. This reverses the 2026-09-14 "Rejected —
  put the trust-boundary axioms behind Module Types too", whose reasoning
  weighed only the proving and not the enforcing.
- **`lastIndex` and `lastEntryID` went opposite ways.** `lastIndex` exports
  only the indexed `_at` form, because its value equation is what `term`'s
  and `lastEntryID`'s proofs need and the weak form cannot be strengthened
  back; its five weak call sites in `reset` and `becomeLeader` open the
  predicate with a new two-line accessor, `own_raftLog_acc`.
  `lastEntryID` exports only the weak form, which is what all four of its
  callers want, and keeps `_at` as a lemma inside its functor — hidden by
  the ascription, same move `Step`'s branch lemmas made on 2026-09-17.
  Rejected in between: a fifth file kind, `derived_<fn>.v`, with a functor
  from the signature to the corollary. It would have worked; it adds a file
  kind everything has to learn, against `CLAUDE.md`'s rule on structure.
- **`Import P.` at the top of each functor**, so that a callee moving into
  `P` does not require rewriting its call sites. This was deliberate on
  `proof_raft__Step_MsgVote_gt.v`, which takes 2:39 and 2.3 GB to check: an
  edit to that file that is not the point of the change is an edit worth not
  making.

### Two specs named after the wrong Go function

- **`wp_raft__appendEmptyEntry` specifies the method `appendEntry`.**
  `appendEmptyEntry` occurs nowhere in the generated code —
  `grep -c appendEmptyEntry new/code/go_etcd_io/raft/v3.v` is `0`. This is
  the axiom that was the *first* false statement recorded in
  [false-statements.md](false-statements.md), and a spec named after a
  function that does not exist cannot be read against a body, which is the
  check that would have caught it. Renamed `wp_raft__appendEntry`.
- `wp_campaign_peer_ids` specifies `quorum.JointConfig.IDs`, naming neither
  receiver nor method — so a second spec of `IDs` would not have collided
  with it, and `Include`-collision is the mechanism that makes a duplicate a
  build error. Renamed `wp_JointConfig__IDs`.

### The duplicate that is still open

`raft.stepLeader` has two triples: the election one
(`own_raft_phys`, `MsgVoteResp`, `Qed`) and `readonly.v:936`'s
`wp_raft__stepLeader_MsgReadIndex` (`r ↦ rf ∗ own_raft γ rf`, `MsgReadIndex`,
postcondition `True`, `Admitted`, no users). The preconditions are disjoint
on `m.Type` so the statements do not contradict; the **ownership** stories
do, and only one of `own_raft` / `own_raft_phys` can survive. Written up in
[false-statements.md](false-statements.md) and now step 8 of STATUS.md's
next steps, together with the other ten loose triples in `readonly.v` and
`protocol.v` that this pass did not touch.

### Verification

- `make -j8 new/should_build.required_vos` — RC=0, i.e. every statement in
  the CI-reachable tree elaborates. Not a `make ci` run: that needs a full
  `.vo` build of Perennial, which nothing in this tree has.
- `make -j4` over every `.vok` target in the election closure — **193 files,
  0 errors, make exit 0**, about 25 min wall. `vos` accepts a proof script
  that does not run; `vok` is the real check. The only non-warning output is
  the `Show.` that `wp_raft__resetRandomizedElectionTimeout`'s `Admitted`
  proof has always carried.
- `etc/check-module-discipline.py --scope election` — RC=0, 0 findings.
  `--selftest` — ok. `--scope raft` — 12 errors, all in `readonly.v` and
  `protocol.v`.

  Two traps met while doing this, worth knowing for the next big move: the
  `%.vok` rule re-runs every time (the stamp does not stick), so a vok sweep
  is always a full sweep and there is no point editing files mid-run; and a
  `.v` edit that triggers a *partial* `vos` rebuild leaves the tree with
  `.vos` files built against different versions of a dependency, which shows
  up as `Error: Compiled library … makes inconsistent assumptions over
  library …` at the aggregator rather than where the edit was. Rebuild the
  whole `vos` closure after editing, then sweep.
- Trust base, counted with comments stripped, base `a21dce0ef` vs now:
  **the same 6 axioms and the same 7 `Admitted`s.** The restructure moved
  them and changed none of them. (Both raw greps over-count, because doc
  comments quote probe lemmas ending in `Admitted.`;
  `etc/check-module-discipline.py`'s `strip_comments` is the helper.)

### Dead ends and traps

- `Local Ltac` inside `Section proof` is invisible to importers even without
  `Local` — a section closes over `Ltac` too. `split_unstable` had to move
  *above* the section, where `intros_ambient` and `wp_log` already were.
- Slicing a Rocq doc comment with a non-greedy `.*?\\*\\)` silently takes a
  prefix when the block contains a nested `(* … *)`, which several of these
  comments do (worked examples, probe lemmas). Two spec files ended up with
  an unterminated `(**` swallowing their `Module Type`; the checker caught
  it as "declares 0 Module Types". Count depth.
- Both are in [gotchas.md](gotchas.md).

### Note for whoever is next

`notes/STATUS.md` is 460 lines against its own stated budget of ~150
([README.md](README.md)). It was 405 before this session. The "Trust base"
and "Known broken" sections are the bulk and both have topic files they
could move into. Worth doing before it stops being read, which is the
failure mode the budget exists to prevent.
