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
