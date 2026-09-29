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

## 2026-09-17 — the array-indexing blocker is fixed, in Goose and in the model

Branch `worktree-goose-array-index-fix`, off `main` at `0fb5a6dd9`.

`bugs/goose-array-indexref-loads-its-operand.md` is deleted: the defect it
described is fixed. It blocked four lemmas — `wp_campaign_peer_ids`,
`wp_ProgressTracker__TallyVotes`, `wp_ProgressTracker__Visit` and the
`wp_JointConfig__CommittedIndex` axiom in `readonly.v` — and it turned out to
be **three** separate Goose bugs plus one genuinely missing model rule, not
the two the bug file had diagnosed.

### What was actually wrong

All three Goose bugs are in `goose/goose.go`, and all three come from array
operations being treated like slice operations.

1. **`exprAddr`, the `*ast.IndexExpr` case.** It used `ctx.expr(e.X)` — a
   *load* — as the operand of `IndexRef`, for every index target. That is
   right for a slice, because a `slice.t` value carries `slice.ptr`, so an
   address can be recovered from it. It is wrong for an array: `array.t` is
   `array.mk n (list V)` and carries no address at all, so `IndexRef` on a
   loaded array value has nothing to take a reference into and no rule can be
   given for it. Fixed by dispatching on `targetTy.Underlying()` and using
   `ctx.exprAddr(e.X)` for arrays.

2. **`sliceExpr`.** Same shape: `$s` was bound to the loaded array. Also
   *semantically* wrong independently of the model — in Go `a[:n]` aliases
   `a`, and a slice of a copy does not. Fixed the same way. The model's own
   `composite_literal_slice` (`new/golang/defn/slice.v:167`) already slices an
   array by address with a literal high index, which is exactly the shape
   Goose now emits, so this was the intended shape all along.

3. **`maybeHandleSpecialBuiltin`, the `len`/`cap` case — the one the bug file
   missed.** It emitted `FuncResolve go.len [T] #()` *with no operand
   applied* whenever `go/types` did not record a `*types.Signature` for the
   builtin. `go/types` omits the signature exactly when the call is
   constant-folded, which for an array operand is always. So the emitted
   expression was a **function value used as an integer**:

       (FuncResolve go.len [go.ArrayType 7 go.uint64] #()) ≥⟨go.int⟩ ![go.int] "n"

   This matters for the record: the bug file's proposed fix — add a
   `FuncUnfold go.len [go.ArrayType n t]` instance — **would not have fixed
   it on its own.** Unfolding `go.len` there yields a lambda that nothing
   applies, so the comparison would still have been against a closure. Goose
   now emits the constant (`#(W64 7)`), which is also what Go's own semantics
   say: `len` of an array is a constant expression.

   Emitting the constant is worth more than a model rule for a second reason:
   the applied form would have forced every array `len` to *load the whole
   array*, so a proof would need ownership of it — and for `len(isLocalMsg)`
   on a package-level `[23]bool`, ownership of a global. Go's `len` needs
   neither.

4. **The missing model rule, which is still needed.** There was no
   `FuncUnfold go.len [go.ArrayType n t]` anywhere under `new/golang/`
   (`go.len_underlying` cannot help: an array type is its own underlying
   type). Goose's constant folding covers every site in the etcd code, but
   not the non-constant case (`len(f())`), so the rule is added.

### The TCB change, and how it is guarded

`new/golang/defn/array.v` gains `len_array` and `cap_array`:

    #[global] len_array n elem_type `{!st ↓u go.ArrayType n elem_type} ::
      FuncUnfold go.len [st]
      (λ: <>, if decide (0 ≤ n < 2^63) then #(W64 n) else AngelicExit #())%V;

Three deliberate choices:

- **Stated at `st ↓u go.ArrayType n elem_type`, not at the literal
  `go.ArrayType`.** `quorum.JointConfig` is a *named* array type, and the
  literal form would not have covered it. This is the mistake `new/golang/defn/map.v`
  makes — its `FuncUnfold`s are at the literal `go.MapType`, which is why
  `wp_ProgressMap_len` in `election/inv_tracker.v` exists as a workaround.
- **Guarded with `AngelicExit`**, matching `array_length_step` and
  `load_array` in the same file. Unguarded, the rule would claim
  `W64 n = n` for array lengths no Go program can have; guarded, it is a
  faithful statement about Go. The guard is the reason a `PureWp` instance
  was needed as well — see below.
- **`λ: <>` discards the operand.** The operand is still evaluated, which is
  what Go does in the non-constant case; in the constant case Go does not
  evaluate it, but Goose folds those, so this rule never sees them.
- `cap` is added alongside `len` because the Go spec gives arrays the same
  answer for both, and leaving it out would leave a hole that shows up later
  as "stuck".

The guard means `wp_auto` alone stops at the Gallina `if decide …`, so
`new/golang/theory/array.v` gets matching `PureWp` instances
(`pure_wp_array_len`, `pure_wp_array_cap`) whose side condition
`0 ≤ n < 2^63` is discharged by the `try done` that `wp_pure` already runs on
a `PureWp` side condition. That is the `pure_wp_slice_len` pattern
(`new/golang/theory/slice.v:335`), with a non-trivial `φ` for the first time
in this development. `array.v` now imports `auto` for `wp_auto_lc`; `auto`
does not reach `array`, so this is not a cycle.

### A circular probe, and what saved it

The first version of the `PureWp` proof was `pure_wp_start. by iFrame.`, which
**passed in a scratch file and failed inside `array.v`**. The scratch file
imported the already-compiled `array.vos`, so `pure_wp_start`'s `wp_pures`
used *the very instance being restated* to discharge it. Inside `array.v` the
instance does not exist yet and the goal is untouched. The real proof has to
go through `func_unfold` and `decide_True`.

**A probe that restates the lemma it is checking is worthless if the lemma is
already compiled.** The probes that meant something were the end-to-end ones
— `WP (FuncResolve go.len [go.ArrayType 7 go.uint64] #() #())` against a
concrete `Φ` — because they can only be closed by the instance doing real
work. Four of those are `Qed`: array `len`, array `cap`, `IndexRef` on an
address, `Slice` on an address, each with no stray side goal.

### Evidence that the fix is load-bearing

- **The old emitted form is genuinely stuck.** `wp_auto` on
  `IndexRef (go.ArrayType 7 go.uint64) (#a, #(W64 0))` with `a : array.t w64 7`
  leaves the goal **byte-for-byte unchanged**. Worth noting against the old
  bug file, which said `wp_auto` "fails with Failed to progress": it does not
  fail, it silently makes no progress. `assert_fails (wp_auto)` therefore
  does *not* detect this — it reports success. Check the goal, not the exit
  status.
- **The real proof gets past it.** In `wp_campaign_peer_ids` the banked
  prefix's last `wp_auto` now steps
  `IndexRef quorum.JointConfig (#c_ptr, #(W64 0))` to
  `#(array_index_ref map.t 0 c_ptr)` and stops at the *load* of that
  location. That is an ownership obligation (`array_acc` on `c`, with
  `Hvoters_arr` for the lookup), not a missing rule.

### Regeneration

Full re-translation, the same invocation `etc/ci-goose-check.py` uses, against
all five pinned Go repos. Six generated files changed and **every changed
line is an array site**: `quorum.v`, `tracker.v`, `v3.v`, `math/bits.v`, and
the two goose testdata files. Zero `IndexRef`/`Slice` operands of the form
`![go.ArrayType …]` remain anywhere in `new/code/`. `new/generatedproof/` is
untouched.

`goose/testdata/examples/unittest/array.go` already exercises all four cases
(element read, `&x[1]` as a pointer receiver, `len`/`cap` in a loop bound,
`x[:]`), so it is the regression harness — no new test data was needed.

Building Goose needs a Go toolchain, which this box did not have; `go1.25.1`
unpacked into the job's scratch directory was enough, and `go build` then
fetched `go1.26.0` itself per `go.mod`.

### A second, separate defect, now measured

The old bug file flagged `len` of a **nil map** as a second obstacle on
`TallyVotes` and recorded it as *not probed*. It is now probed and it is
stuck: `wp_auto` leaves
`#(functions go.len [go.MapType go.uint64 go.bool]) (#map.nil)` untouched.
`go.len_map` unfolds to `InternalMapLength (Read "m")`, and at `map.nil` that
is a read of the null location, while Go says `len(nil map) = 0`. There is no
nil case for `go.len` the way there is one for ranging
(`wp_map_nil_for_range`), and no `PureWp` for map `len` at all. Filed as
`bugs/golang-len-of-nil-map-is-stuck.md`. Not fixed here — it is a different
defect and a separate TCB decision.

### Re-verification

A **TCB change adds global instances, so the existing proofs have to be
re-checked.** Done from a clean slate: every `.vos`/`.vok` deleted, the
closure rebuilt (248 files, rc=0), then `-vok` over every file with proofs in
it — `new/golang/defn/*.v`, `new/golang/theory/*.v`, the whole
`v3_proof/election/`, `v3_proof/*.v` and `v3_proof/../raft/*.v`.

**101 files, 0 FAIL, 0 ERRORS.** Including the three that carry the most
regression risk from the new instances — `new/golang/theory/slice.v`,
`theory/map.v` and `theory/array.v`, where `pure_wp_array_len` is now a
candidate alongside `pure_wp_slice_len` for every `go.len` redex — and the
single big `proof_raft__Step.v` (this branch is off `main`, so it predates the
perf branch's nine-way split).

Resolution order is not a problem: a slice `len` tries `pure_wp_array_len`
first, fails `go.SliceType t ↓u go.ArrayType ?n ?e` after one instance
resolution, and backtracks. Constant cost per redex, not linear in the
program text.

The **cleanup pass on `goose.go`** (hoisting `ctx.expr(e.X)` inside the
branches instead of computing and discarding it — `Ctx` carries mutable state
like `usesDefer` and `out`, so a discarded `ctx.expr` is a latent hazard) was
checked by re-translating into a scratch directory and diffing: all six
affected files **byte-identical** to what is committed. So `check-goose` will
pass.

### Where to pick up

`wp_campaign_peer_ids` is the cheapest remaining win on the election path and
is now ordinary proof work: `array_acc` on `c` for element 0, then
`wp_map_for_range` over `voters_ref`, then `wp_map_nil_for_range` at index 1,
then `return: m`. `wp_ProgressTracker__Visit` and the
`wp_JointConfig__CommittedIndex` axiom are unblocked the same way.
`TallyVotes` needs the nil-map `len` gap closed first, and separately its
`VoteWon` conjunct repaired.

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
  `--selftest` — ok. Over the whole raft proof — 12 errors, all in
  `readonly.v` and `protocol.v`.

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

---

## 2026-09-18 (later) — `Step`'s eight proof helpers move to `proof_raft__Step_helpers/`

Same branch, follow-on to the entry above.

### Why

The collection layout makes the top-level election directory the thing you
audit: four files per Go function, and you can check "one spec per function"
by reading it. After the morning's work it held 176 collection files, eight
shared files — and eight that were neither, `Step`'s branch lemmas, sorting
in among the collections and indistinguishable from collection members by
name. `proof_raft__Step_MsgVote_gt.v` looks exactly like the proof file of a
collection whose spec someone forgot. That defeats the point of the layout.

### What moved

`proof_raft__Step_MsgHup.v`, `_MsgVote.v`, `_MsgVoteResp.v`,
`_MsgVote_gt.v`, `_MsgVote_le.v`, `_MsgVote_lt.v`, `_MsgVote_eq_novote.v`
and `_MsgVote_eq_voted.v` → `election/proof_raft__Step_helpers/`. `Step` is
the only function whose proof spans more than one file, so it is the only
directory. File names kept; see the decision record for why not shortened.

The only code change beyond the `git mv` is three `Require Export` lines —
the ones *pointing at* the moved files, in `proof_raft__Step.v`,
`_MsgVote.v` and `_MsgVote_le.v`. The helpers' own
`Require Export …election.postulates_raft__Step` is an absolute logical
path and did not move, which is the thing to know before attempting a
rearrangement like this: only inbound references break.

`proof_<fn>_helpers/` rather than `proof_<fn>/`, because a directory
`election/proof_raft__Step/` would collide with the file
`election/proof_raft__Step.v` for the logical name
`…election.proof_raft__Step`. Worth knowing generally: under `-Q new New` a
directory and a `.v` file of the same name in the same parent cannot
coexist.

### Made a rule

`etc/check-module-discipline.py` gained `H1` (a helper at the top level),
`H2` (a `Module Type` or an assumption inside a helpers directory — a spec
hiding in proof structure) and `H3` (a helpers directory with no
`proof_<fn>.v`). `H1` is structural, not a filename list: a
`proof_<X>_<suffix>.v` whose own collection has no spec while `<X>` does is a
helper by construction. `--summary` now names the functions that have helper
directories.

All three were verified by planting a violation rather than by reading the
code: a copied helper at the top level (H1 fired), a two-line
`Module Type`/`Parameter` file inside the directory (H2 fired twice, once for
each), and a `proof_zznothing_helpers/` with nothing to help (H3 fired).
Then deleted.

### Verification

- `rm .rocqdeps.d && make -j8 new/should_build.required_vos` — RC=0. The
  dependency file has to be deleted: it is generated, and it still named the
  old paths.
- `make -j4` over all 193 `.vok` targets in the election closure, now found
  with `find` rather than a top-level glob so the helpers directory is
  included — see below for the result.
- `etc/check-module-discipline.py --scope election` RC=0, `--selftest` ok.
  193 targets, `MAKE_EXIT=0`, 0 errors; the sweep script now finds its
  targets with `find` rather than a top-level glob, so the helpers directory
  is included (checked: 178 of the log's lines name it).

### And then: the checker was specialized to this proof, so that was removed

A separate pass over `etc/check-module-discipline.py`, after Upamanyu asked
for it to be as generic as sensible. Four specializations, all in the
*logic* rather than in the examples:

- `suggest_name` had `if parts[0] == "raft": return parts[1]` — a package
  name deciding naming policy. Replaced by `acceptable_names`, which returns
  both the bare and the package-prefixed form and lets the author use
  either; the `N1` note now fires only when the collection name is neither.
  This is the right shape anyway: which reads better depends on the package,
  and a checker should not be the thing that decides.
- The proof root, the code roots and a two-entry table of scope names were
  module constants with no way to override them. Now `--proof-root`,
  `--code-root` (repeatable) and a `--scope` that takes a path *or* the bare
  name of any directory under the proof root — which is the convenience the
  hardcoded table was providing, generalised.
- The code index dropped Rocq's module alias and matched on `Type.method`
  alone, justified in a comment by "distinctive enough across these five
  packages". It now resolves the alias against the `Module` declarations each
  generated file makes, with the bare name as a fallback, so a package
  translated into a file of any name resolves properly. (This is why
  `raft.raft.poll` works at all: the raft package is `new/code/.../v3.v`.)
- Goose's `Recv__method` separator and the collection-naming separator were
  one constant. Same spelling, different conventions; split.

Verified by pointing it at another development: `--proof-root
new/proof/go_etcd_io/etcd` reports 24 out-of-place triples, and the raft and
election numbers are unchanged (12 errors and 0). The self-test cases for the
naming and lookup helpers now use `pkg`/`Type`/`fn` placeholders instead of
real names, so they assert the convention rather than this proof's contents.

What deliberately stays: the module docstring and the parsing self-test use
real Goose output shapes as examples, because a regex for
`@! (go.PointerType <pkg>.<Type>) @! "<method>"` is unreadable without one.

## 2026-09-18 — review of the module-discipline branch

A low-effort correctness pass over `main...worktree-module-discipline` (the
`wp_auto`/`proofmode` speedups, the one-collection-per-function split, and
`etc/check-module-discipline.py`) found a real bug in
`spec_raft__appendEntry.v`, the trust-boundary axiom the rename earlier in
the day had touched: it claimed `RET #true` for an arbitrary `es` and took no
ownership of `es`, while `raft__appendEntryⁱᵐᵖˡ` has a `return: #false` path
and writes `Term`/`Index` into every element of the slice. Both real; the
ownership one is `wp_ProgressTracker__Visit` one level out.

**Its proposed fix was wrong, and the way it was wrong is the lesson.** The
review weakened the result to an existential `accepted : bool` on the grounds
that "`becomeLeader`, the only caller in scope, ignores it". `becomeLeader`
does not ignore it:

    if !r.appendEntry(pb.Entry{Data: nil}) { r.logger.Panic("empty entry was dropped") }

`wp_Logger__logf` deliberately excludes `Panic`, so the existential form
makes `becomeLeader` unprovable rather than merely weaker. Measured by
installing the review's version and building it: `election.required_vos`
rc=0, `proof_raft__becomeLeader.vok` rc=2, `Error: Failed to progress.` —
`wp_auto` cannot step `if: ~accepted` for an opaque boolean. Third time in
this session that a `vos`-green change was wrong; the review said the edit
was "mechanical" and flagged that it had not built it, which is the only
reason this was caught rather than pushed.

The repair keeps `RET #true` and adds the premise that makes it true:
`increaseUncommittedSize` rejects only when `payloadsSize(ents) > 0`
(`v3.v:5401`, and `payloadsSize` sums `len(e.Data)` at `v3.v:7515,7524`), so
`Forall (λ e, sint.Z e.(Entry.Data').(slice.len) = 0) ents` — exactly what
`becomeLeader` passes — makes the `Panic` demonstrably dead code. The slice
is owned as a precondition and handed back existentially, since
`raftLog.append` copies values rather than taking the slice.
`becomeLeader` discharges the premise with `apply Forall_singleton. done.`

Verified: `proof_raft__becomeLeader.vok` rc=0 with the repair, and the full
193-target sweep re-run afterwards. Both write-ups in
notes/false-statements.md, including the two tells — an argument the triple
says nothing about, and a weakening that breaks a caller.

One detour worth recording, because it cost a whole sweep. The probe above
saved and restored the two files with `shutil.copy2`, which preserves
mtimes — so the `.vos` built from the review's version came out *newer* than
the restored corrected source, `make` skipped rebuilding it, and the next
sweep compiled `becomeLeader` against a spec that was no longer in the tree.
It failed with `iAndDestruct: cannot destruct (own_raft_phys …)`, which reads
like a proof bug and is not one. `touch` the restored files and rebuild the
whole `vos` closure. Written up in [gotchas.md](gotchas.md).

The rest of the diff came back clean at this effort level. The framework
changes worth a second reader some day, none of them a finding: `Ltac done
::=` in `proofmode.v` globally weakens `done` on `WP` goals for the whole
downstream build (deliberate, documented); `wp_pure_candidate`'s shape filter
silently skips the `PureWp` search for any listed node with an unevaluated
operand, so a future instance that steps such a node would need adding
there; and `wp_done_core`'s comment says "copied verbatim" from stdpp while
the `¬_` arm is deliberately `fast_done` rather than a recursive `done`.

---

## 2026-09-18 (later) — a TCB viewer: `etc/tcb-report.py`, and a shared parser

Claude Opus 5 (background job), at Upamanyu's request: "it is challenging to
quickly identify incomplete parts of the proof", so a generic tool showing a
file-by-file status and an overall measure of the size of the TCB —
"theorem statements for externally facing functions; specs for internal
functions are just untrusted proof artifacts".

Branch `tcb-view`, off `main` at 43660bd0f.

- **Did:**
  - **`etc/rocqscan.py`** (new) — the shallow Rocq scanning both tools need:
    comments, sentence ends, what a sentence declares and inside which
    modules, how a proof ended, a record's fields and an inductive's
    constructors, `Require` lines, and which Go function a triple's program
    expression names. Lifted out of `check-module-discipline.py`, which now
    imports it. Own self-test: `python3 etc/rocqscan.py`.
  - **`etc/tcb-report.py`** (new) — the viewer. `--view summary` (default),
    `files`, `assumed`, `surface`, `all`; `--scope`, `--proof-root`,
    `--format json`, `--selftest`. Always exits 0.
  - **`etc/check-module-discipline.py`** — parser removed, imports added,
    `--selftest` now runs rocqscan's too. **Output is byte-identical** before
    and after on `--scope election --summary`, the whole raft tree, and
    `--format json`, with the same exit codes; that diff was the acceptance
    test for the refactor.
  - Documented in `CONTRIBUTING.md`, `notes/STATUS.md` ("Trust base" no
    longer tells you to grep) and `notes/decisions.md`.

- **What it says today** (whole raft proof, 198 files, 8,841 lines): 45
  assumed (31 `Axiom`, 14 `Admitted`; 18 triples, 13 model properties, 14
  opaque declarations, 2 marked `Trusted`), 7 exported results, 85
  definitions reached from those statements — 866 lines, 9.8%. Not trusted:
  44 discharged obligations, 43 internal function specs, 114 `Qed`s. The
  election path: 6 axioms, 7 admits, 43 definitions, 395 lines.

- **Checked against the hand counts, which were right.** An independent
  recount written not to share the tool's logic — strip comments, count
  `Admitted.`, count assumption keywords outside a `Module Type` found by a
  separate bracket scan — agrees file by file: 14 `Admitted`, 31 `Axiom`.
  The election path's 6 and 7 are the same 6 and 7 `STATUS.md` listed by
  name.

- **What did not work, in order:**
  - **Go's export rule as the definition of "externally facing".** The
    obvious reading of the request, and wrong: `quorum.JointConfig.IDs` is
    exported and is an internal callee, while `raft.raft.poll` is
    unexported. What works is "nothing in the development depends on it".
    Go's rule is still reported next to each result, because an *unexported*
    exported result is worth a second look.
  - **Counting `election.v`'s `Require Export link_*` as uses.** That file
    re-exports every collection so `make ci` builds them, so every
    collection looked internal and the development came out with no exported
    result at all. Only a require or a mention from another *collection*
    counts, and `raft__Step` is then the single root — which is what the
    call graph actually is.
  - **Reading only statements for the "is it used" test.** A lemma is used
    by being applied in a proof script, so `readonly.v`'s helpers
    (`quorums_intersect`, `big_sepL2_drop`, …) all looked like exported
    results: 29 of them. Scanning proof bodies too — kept separate from the
    statement references, which are what the definition closure follows —
    cut it to 11.
  - **`Example rwmutexMaxReaders_ok : … := eq_refl.`** read as a proof with
    no terminator. A provable keyword with no proof and a `:=` is a
    definition by term; both halves of that test are needed, since a
    statement can hold a `let … :=` and still be proved by a script.
  - **`--scope election` swallowed `election_protocol.v`**, because
    containment was a string prefix. Compare path components.
  - A list-aliasing bug in the module-stack tracker: `End` popped in place a
    list earlier snapshots shared, so every declaration came out at the top
    level. Caught by the self-test, which is why that test pins the module
    path of a `Record` inside `Module msg.`.

- **Surprises worth keeping:**
  - The definitions are the larger half of the trust base — 651 lines
    against 127 — and no count of axioms shows them. That is the substantive
    reason this is not just a fancier `grep -c`.
  - The tool disagrees with nothing in the notes, but it *reclassifies*: an
    `Axiom` that introduces an opaque predicate (`own_raft_ghost : … → iProp
    Σ`) is a different thing to trust from one that asserts a property
    (`is_leader_unique`). 14 of the 31 axioms are declarations.
  - Pointed at `new/proof` it finds 6 files with `Abort`ed proofs, four of
    them in Goose's own semantics test data.

- **Left:** `ruff` could not be run — no `pip`, no network in the sandbox —
  so the three Python files are formatted by hand to match their neighbours
  and CI's `ruff format --diff` job has not been reproduced locally. Worth a
  single `ruff format` pass before merge. Nothing else is outstanding; the
  three self-tests and the byte-identical-output check all pass.

---

## 2026-09-18 — review of the array fix: is the translation-time dispatch justified?

Review question on the 2026-09-17 fix: branching on array-vs-slice *in Goose*
cuts against Goose's preference for leaving type dispatch to the Rocq
semantics. Is it necessary, and is it correct — e.g. can you write `f()[:]`
where `f` returns `[10]int`, which the fix would reject because `f()` is not
addressable?

Answered with the Go compiler rather than from the spec alone.

### `f()[:]` is not legal Go

    ./a.go:6:35: cannot slice unaddressable value f() (value of type [10]int)

The spec requires the operand of a slice expression to be addressable when it
is an array. Goose runs after go/types, so it never sees such a program. The
measured boundary:

| expression | legal? |
|---|---|
| `f()[0]` (array-returning `f`), read only | **yes** |
| `&f()[0]` | no — "cannot take address of" |
| `f()[:]` | no — "cannot slice unaddressable value" |
| `m[0][:]` (`m` a map to array) | no — map values are not addressable |
| `p[:]`, `p[0]`, `&p[0]` for `p *[10]int` | **yes** |
| `a[:]`, `&a[3]`, `aa[0][:]`, `s.a[:]` | **yes** |

### The dispatch cannot be pushed into Rocq

Both uniform alternatives are closed:

- **Always pass the value** is the original bug: an `array.t` carries no
  address, so no `IndexRef` rule can be written for it.
- **Always pass the address** is impossible, and this is the decisive half:
  `&fs()[0]` is *legal Go* when `fs` returns a **slice**. Slice elements are
  addressable even though `fs()` is not, so `exprAddr(fs())` does not exist.
  Checked: it compiles, and Goose emits the slice-value form for it.

So the operand kind genuinely differs between arrays and slices and the choice
is forced by the static type. Go itself draws the line statically and for the
same underlying reason: a slice value contains a pointer, an array value does
not. `ctx.expr` already branches on `Types[e].Addressable()` for *every*
expression, and `indexExpr`, `assignFromTo` and `getIndexType` already switch
on `*types.Map`/`*types.Array` in the same functions, so this is consistent
with local practice rather than a new principle.

The invariant that makes the change safe: `exprAddr` is only ever called on an
addressable expression, and Go makes `a[i]` addressable iff `a` is (for an
array), so the `exprAddr(e.X)` in the `IndexExpr` case is always defined. Note
also that the *old* code called `ctx.expr(e.X)`, which for an addressable
operand is `DerefExpr{X: exprAddr(e.X)}` — it already went through `exprAddr`.
So the fix cannot introduce a new `exprAddr` failure on any operand the old
code handled. Both reasons are now comments in `goose/goose.go`.

### A/B against `main`'s Goose

Same input, both translators, over `f()[0]`, `p[:]`, `p[0]`, `&p[0]`,
`a[:]`, `s.a[:]`, `len(f())`, `len(s.a)`, `aa[0][:]`, `&aa[0][3]`,
`&fs()[0]`, `fs()[:]`:

- identical failures — **2 errors in each**, at the same positions, both
  `getIndexType: unexpected type for indexing` on `p[0]` and `&p[0]`. The fix
  introduces **no new rejections**.
- on everything that translates, the only lines that differ are array sites.
  Slice paths (`&fs()[0]` → `IndexRef (go.SliceType …) (fs() #(), …)`,
  `fs()[:]`) are untouched.
- nesting composes correctly: `aa[0][:]` becomes
  `Slice (go.ArrayType 10 go.int) (IndexRef (go.ArrayType 3 (go.ArrayType 10 go.int)) ("aa", #(W64 0)), …)`
  — the inner `IndexRef` produces exactly the address the outer `Slice` wants.

### Where the criticism does land: `len`/`cap`

This part was a *choice*; the model rule alone could have carried it, by
emitting the applied form uniformly and letting `go.len_array` dispatch. The
defence is faithfulness, not convenience: Go says `len`/`cap` of an array **is
a constant expression** and does not evaluate the operand, so emitting the
applied form would make the model perform a load the real program never
does, and demand ownership Go does not need — `len(isLocalMsg)` on a
package-level `[23]bool` would require owning a global. The test added is also
`Types[s].Value != nil` ("did go/types fold this?"), not an array/slice test,
which is arguably *less* type dispatch than the code it replaced.

If the maintainer prefers maximal Rocq dispatch anyway, **this is the
separable piece** — reverting just the `len`/`cap` case leaves the
`IndexRef`/`Slice` fix intact, at the cost of array loads in proofs (today
blocked anyway, since `into_val_typed_array` is `Admitted`). The
`IndexRef`/`Slice` half is not separable.

The model rule is not dead weight either way: `len(f())` is non-constant, so
go/types gives the builtin a signature, Goose emits
`let: "$a0" := f() in (FuncResolve go.len [go.ArrayType 10 go.int] #()) "$a0"`,
and that needs `go.len_array`. Confirmed by translating it.

### Pre-existing gap found while reviewing, not fixed

**Pointer to array is unsupported**: `p[:]`, `p[0]` and `&p[0]` for
`p *[10]int` are all legal Go. `p[0]`/`&p[0]` fail in `getIndexType`, which
switches on Slice/Map/Array and has no `Pointer` case; `p[:]` translates but
emits `Slice` on a `go.PointerType`, for which the model has no rule. Both
predate this fix and are unchanged by it. No raft code hits it, so it does not
meet the `bugs/` bar ("a proof cannot be completed"); recorded here so the
next person who trips on it knows it is known.

## 2026-09-19 — ruff, and what it says about the repo

Claude Opus 5 (background job). Closes the item the previous entry left
open: `ruff` *is* installable here, by downloading the 0.16.5 release binary
rather than through `pip`, which is absent. Branch `tcb-view`.

- **Did:** `ruff format` and `ruff check --fix` over `etc/rocqscan.py`,
  `etc/tcb-report.py` and `etc/check-module-discipline.py`, then the seven
  findings ruff would not fix itself by hand — six `ISC004` (an implicitly
  concatenated string inside a tuple needs its own parentheses, so a missing
  comma cannot masquerade as concatenation; they are in the self-test table
  the scanner inherited) and one `SIM102`. **All three files are now clean
  under both jobs.**

- **Verified, because a reformat that changes behaviour is the whole risk:**
  `check-module-discipline.py` still produces byte-identical output on all
  four invocations (`--scope election --summary`, the raft tree,
  `--format json`, `--proof-root new/proof`), `tcb-report.py --view all` is
  byte-identical across the reformat, the three self-tests pass, and the
  independent recount still says 14 `Admitted` / 31 `Axiom`. The fixes are
  not all cosmetic — `.format()` became f-strings throughout and
  `body[:-1]` became `body.removesuffix(".")` — which is why this was
  checked rather than assumed.

- **What ruff says about the rest of the repo, which is the finding worth
  recording.** CI's `python` job runs `ruff format --diff` and `ruff check`.
  On `main`, *both* were already failing:

  | | on `main` | on this branch |
  |---|---|---|
  | `ruff format --check` | 1 file unformatted | **clean** (43 files) |
  | `ruff check` | 99 errors in 11 files | 64 errors in 11 files |

  The one unformatted file on `main` was `etc/check-module-discipline.py`,
  so this branch turns the format job green. The 64 remaining lint errors
  are **all pre-existing and none of them are in this branch's files**: 25
  in `etc/semantics-coverage.py`, 9 in `etc/rocqc.py`, 6 each in
  `etc/test_coqc.py` and `etc/ci-goose-check.py`, 5 in
  `new/etc/update-goose-new.py`, and the rest scattered — 47 of the 64 are
  auto-fixable.

  Mostly `UP032` (use an f-string) and `UP006` (`List[x]` → `list[x]`), so
  the enabled rule set and the house style of `etc/` have simply disagreed
  for a while and nobody noticed, because the job was already red.

- **Deliberately not fixed here.** Cleaning 11 unrelated scripts would
  triple this branch's diff and mix a tooling feature with a lint sweep, and
  two of the files (`new/proof/github_com/mit_pdos/perennial/goose/model/…/
  paradox.py`, `new/experiments/gencongruence.py`) are Perennial-inherited,
  where [decisions.md](decisions.md) says to keep upstream merges
  mechanical. It wants its own branch, and `new/etc/update-goose-new.py`
  should be exercised against a real Goose run before anyone touches it.

- **Left:** the lint job stays red until that sweep happens. `ruff` is at
  `~/.local/bin/ruff` on this box, version-matched to the pin in
  `pyproject.toml`.

---

## 2026-09-19 (later) — the rest of the ruff errors, and what they were hiding

Claude Opus 5 (background job), at Upamanyu's request: fix all of them, not
just this branch's. **Both CI python jobs are now green for the first time
since the rule set and the house style diverged** — `ruff format --check`
over 43 files and `ruff check` over the repo.

- **52 by `ruff check --fix`** (import sorting, `.format()` → f-strings,
  `List[x]` → `list[x]`, `removeprefix`/`removesuffix`, `print("")` →
  `print()`, an unused `# ruff: noqa`), across `etc/semantics-coverage.py`,
  `etc/rocqc.py`, `etc/test_coqc.py`, `etc/ci-goose-check.py`,
  `etc/timing-report.py`, `etc/int_template.py`, `etc/trace-deps.py`,
  `etc/get-deps.py`, `new/etc/update-goose-new.py`,
  `new/experiments/gencongruence.py` and Goose's `paradox.py`.

- **14 by hand**, of which two needed a decision rather than a keystroke:

  - **`PLW1510` x4 in `etc/ci-goose-check.py` was a false positive with a
    trap in it.** The four flagged `sp.run` calls *do* pass `check=True` —
    through `**shared_args`, which ruff cannot see into. Adding `check=`
    beside the unpacking, which is what the rule's message suggests, would
    have raised `TypeError: got multiple values for keyword argument
    'check'` the next time CI ran a Goose check. The fix was to drop the
    dict and pass `check=True, cwd=path` at each site.
  - **`DTZ005` x4 has to move as a unit.** `rocqc.py` subtracts two
    `datetime.now()`s to get a compile time and `test_coqc.py` constructs
    the `start` it passes in; making one side aware and not the other
    raises on the subtraction. Both moved to `datetime.now(timezone.utc)`.
    Nothing is stored but the delta, so no recorded value changes — and the
    delta can no longer jump an hour across a DST change. `timezone.utc`
    and not `datetime.UTC`: ruff accepts either, and the alias would have
    quietly raised the floor to Python 3.11.

  The rest: `BLE001` got a `noqa` with a reason (a CLI's top-level handler
  is meant to catch everything), `C402` a dict comprehension, `PLR1722`
  `sys.exit`, `RUF059` an underscore, and the two `EXE001`s differently —
  `chmod +x` for the inherited `paradox.py`, because a mode change never
  conflicts on an upstream merge, and deleting the vestigial shebang from
  `etc/test_coqc.py`, which nothing executes.

- **Verified, since a lint sweep that breaks a script is worse than the
  lint.** Every runnable script produces byte-identical output and the same
  exit code before and after (`--help` for six of them;
  `semantics-coverage.py` run for real against `new/proof/github_com/`, from
  the same directory so that its `__file__`-derived paths match). The three
  self-tests pass, `check-module-discipline.py` is still byte-identical to
  pre-refactor `main`, and the TCB numbers are unchanged. `ci-goose-check.py`
  was **not** run: `--help` is not a thing it has, and invoking it clones
  two repositories into `/tmp` — found out the hard way. It was verified by
  reading. `timing-report.py` needs `pandas`, which is absent, so it was
  only compiled.

- **What the sweep turned up, which is the part worth keeping.**
  `etc/test_coqc.py` — the only Python test in the repo — **has been dead
  for some time and in two independent ways.** It imported `coqc`, a module
  renamed to `rocqc.py`, so it could not even load; and with that repaired,
  five of its six tests fail with `TypeError: cannot use a bytes pattern on
  a string-like object`, because `Classify`'s regexes became `rb"..."` when
  the filter moved to reading `rocq compile`'s output as bytes, and the
  fixtures were never ported. Nothing runs it — no Makefile target, no CI
  job, and `pytest` is not a dependency — which is why neither rotted
  loudly. The import is fixed and the file now carries a comment saying all
  of this, so that a green import is not mistaken for a green test.

- **Left:** porting `test_coqc.py`'s fixtures to bytes, and deciding whether
  anything should run it. Both are somebody's afternoon, and neither is on
  the raft proof's critical path.

## 2026-09-19 (later) — closing the election admits: setup, and two model fixes

Goal for this line of work (branch `worktree-election-close-admits`): every
Hoare triple on the election path `Qed`, so that what remains assumed in the
raft proof is the protocol layer of `election_protocol.v` (12 ghost-state
axioms) plus the declared trust boundary. The tracker is the table at the top
of STATUS.md's "In flight". The ghost layer itself is out of scope here.

- **What `tcb-report` does and does not answer.** Asked whether its output
  is the list of admits to prove for leader election: only partly.
  `--scope election` lists the 8 owed items in `election/` but never sees the
  12 axioms in `election_protocol.v` one directory up, which
  `raft_election_safety` uses *directly* (`own_raft_ghost_is_leader`,
  `is_leader_unique`); the unscoped run sees them but also 20 assumptions
  from `readonly.v`/`protocol.v` that election never touches. The tool has
  no reachability-from-a-theorem view for assumptions (only for
  definitions), and `Print Assumptions` is unavailable without a `.vo`
  build. Worth a `--from <result>` view some day.

- **The Goose array fix arrived via `main`, not by hand.** A first attempt
  here took `goose/`, `new/code/`, `new/golang/{defn,theory}/array.v` and
  `bugs/` straight from `worktree-goose-array-index-fix` (its proof-side
  edits to `inv_misc.v`/`inv_tracker.v` predate the 2026-09-18 collections
  and no longer apply). The maintainer then merged that branch into `main`
  (`d0a281822`), so this branch merged `main` instead; the hand-ported paths
  were byte-identical and merged silently, and only the two notes files
  needed resolving. One thing to know about `git checkout <rev> -- dir`: it
  does not delete files absent in `<rev>`, so the fix's deletion of
  `bugs/goose-array-indexref-loads-its-operand.md` had not been picked up
  by the hand port; the merge did it.

- **`len` of a nil map has a rule now.** `go.len_map`'s body was
  `InternalMapLength (Read "m")`, a read of the null location at `map.nil`;
  the fix branch had measured it stuck and filed
  `bugs/golang-len-of-nil-map-is-stuck.md`. The body now tests for nil first,
  exactly as `lookup2` and `for_range` in the same file do, and returns
  `#(W64 0)` — Go's `len(nil map)`. A TCB change, and a faithful one.
  `theory/map.v` gains `pure_wp_map_nil_len` (so `wp_auto` steps it) and a
  general **`wp_map_len`** for an owned map, which is the proof that had
  been written twice by hand — `wp_map_len_uint64` in `proof_raft__campaign.v`
  (deleted) and `wp_ProgressMap_len` in `inv_tracker.v` (now a two-line
  wrapper doing the named-type rewrite). Both callers had to step past the
  new nil test; `own_map_not_nil` + `wp_if_destruct; first by exfalso`, as
  `wp_map_for_range` already does.

- **Build facts for the next person.** Nothing in the tree was built; the
  `.vos` closure of `election.v` builds from nothing in about six minutes
  with `make -j4` on this 8-core/15 GB box. A checkout that adds a
  `Require` mid-build fails with "Unable to locate library" because
  `.rocqdeps.d` was computed before the edit — re-run `make`, it is not a
  real error. The Rocq toolchain is the `perennial` opam switch
  (`/home/ubuntu/.opam/perennial/bin`), not on the default `PATH`.

## 2026-09-20 — wave 1: two landed, then the rate limit; a `-vok` sweep of the whole tree

- **Landed and committed:** `wp_raft__promotable` (`afd9f4bc2`) and
  `wp_JointConfig__IDs` (`ea56a938f`), each re-checked independently of the
  agent that wrote it. `IDs` found two framework defects in
  `theory/map.v` — `wp_map_for_range` never hands the map back, and the
  nil-map `PureWp` instances (including yesterday's `pure_wp_map_nil_len`)
  are closed over the section's `K V`, so `tc_solve` cannot fire them —
  worked around in a `_helpers/` file; tracker item 14.

- **Four agents died mid-task** (weekly rate limit on the model they ran
  on). What they left is a shared tree with partial edits from all four,
  so rather than trust anyone's last words, every proof-bearing file in
  the election development was checked at `-vok`, four at a time
  (`/home/ubuntu/.claude/jobs/…/sweep.sh`; 79 files, ~35 min wall). Result:
  **74 pass, 5 fail**. The passes include everything that was Qed before
  under the *new* `send` spec and the widened `own_raft_phys`
  (`HelectionTimeout`): `campaign` (402 s), `Step` and all eight helpers,
  `hup`, the `becomeX` family, `stepCandidate`. The fails:
  `inv_raftlog.v` (a `Forall_forall` that resolved to Coq's `In` version —
  fixed on the spot, RC=0), `proof_raft__reset.v` (the RNG spec's new
  premise passed positionally fixes `rv` to the pre-update struct, so
  `iFrame` cannot find `r ↦ rv <| lead := 0 |> …`), `proof_ProgressTracker__Visit.v`
  (an unfinished bullet), `proof_extend.v` and
  `proof_raftLog__mustCheckOutOfBounds.v` (`word` cannot find a witness).
  A sweep like this is the right move whenever several writers have
  touched one checkout and none of them is around to say what state it is
  in; the results file is one line per file and reads in a minute.

- **What the interrupted agents built** (all in the tree, committed as
  such): the general `spec_raft__send.v` with `send_ok`, proved (377 s) and
  every caller re-proved; the RNG chain — `is_initialized` now owns
  `globalRand` with `is_lockedRand` (mutex invariant `True`),
  `ErrCompacted`, `ErrUnavailable`; `rand` has `is_rand_initialized`
  (`Reader`); `inv_big.v` with the abstract `own_big_Int`; axioms
  `rand_Int`, `big_NewInt`, `big_Int__Int64`; `lockedRand__Intn` Qed;
  `resetRandomizedElectionTimeout` Qed with a `0 < electionTimeout` premise
  (crypto/rand panics on a non-positive bound) carried by `own_raft_phys`
  as `HelectionTimeout`. The log chain: `is_Storage` gained an `Entries`
  triple (non-empty, `cap = len`, lent back by wand — matching
  `MemoryStorage`), `hasUnappliedConfChanges`'s spec now owns `r ↦ rv`
  (the old one asserted loads it did not own; `hup` adjusted),
  `scan_closure` and two list/slice helpers in `inv_raftlog.v`, and nine
  callee collections with specs written and proofs mostly `Admitted`.
  `Visit` has a complete-looking `wp_visit` helper proof that does not
  check.

- Continuing with Opus agents, from this verified baseline, one task each:
  `reset.v` call sites; finish `Visit`; the log leaves; `scan` + the
  `hasUnappliedConfChanges` target; `TallyVotes`.

## 2026-09-20 (later) — wave 2 with Opus agents: five landed, two cut off again

- **Landed and committed** (each independently re-checked at `-vok` before
  the commit): `Visit` (`9b9e800ff`), the `reset` call-site fix
  (`f8b044570`), `raftLog.scan` + `hasUnappliedConfChanges` (`507694632`).
  Branch pushed to GitHub as `worktree-election-close-admits`.

- **Proved but not yet committed** — their proofs are checked against a
  shared predicate another agent was still reshaping, so they wait for the
  tree to settle: `TallyVotes` with `JointConfig__VoteResult` and
  `MajorityConfig__VoteResult` (three proofs + `poll` at RC=0), and
  `appendEntry` with six callee collections and `becomeLeader`
  (RC=0 on all, plus seven `is_Storage` dependents). The `appendEntry`
  design — derive the no-wrap bound from `is_Storage`'s new `Hbounded`
  rather than carry it — is in decisions.md.

- **The second rate-limit cut** (Opus session limit) killed `log_leaves`
  and `bcastappend` while both were in their final `-vok` runs. A second
  full sweep (99 files now, 90 pass) shows what `bcastappend`'s rewrite of
  `own_progress`/`own_tracker`/`visit_closure` broke: `IDs`,
  `JointConfig__VoteResult`, `RecordVote`, `ResetVotes`, `TallyVotes`,
  `Progress__BecomeReplicate` and `campaign` (its local
  `own_tracker_cfg_size` no longer closes) — plus its own `bcastAppend`;
  `Visit` and `reset` it had already re-proved. `raftLog__slice` (473 s
  before failing) is the one `log_leaves` file still open. Both agents were
  resumed with these lists at 22:45 UTC.

- **Lesson, stated once for the notes.** The rule "a shared-file change is
  yours to re-check in every dependent" is right, and it is not enough when
  the change is a *reshape* of a predicate ten proofs destructure
  positionally: the writer cannot finish before its neighbours' proofs
  start breaking. The cheaper discipline, used by the `appendEntry` agent
  for `is_Storage`: add clauses, never reorder or rename; destructure with
  `iNamed`, never positionally; and land the shared change as its own
  commit before the proof that needs it.

## 2026-09-21 — waves 3 and 4: the election path is Qed modulo one marked admission

- **Landed** (each independently re-checked before its commit):
  `Inflights.Add` + `Inflights.grow` (`2c41ed8a5`); `raftLog.term` made total
  (`0ee68ef1f`); `maybeSendSnapshot` with `raftLog.snapshot`, `IsEmptySnap`,
  `Progress.BecomeSnapshot` (`ae7fd6884`); and finally `maybeSendAppend`,
  after the `own_raft_bare` split (this commit).

- **What `maybeSendAppend` taught.** Its blocker moved three times, and each
  time the proof itself was fine and a *spec* was wrong: `raftLog.term` was
  partial where the code branches on the error; `maybeSendSnapshot` asked
  for a `Progress` it already owned inside `own_raft_phys`; `send` hid the
  tracker under an existential; and `send` demanded the whole log while the
  caller had to hold a page of it across the call. All four are now in
  false-statements.md as one family with one rule. The repair,
  `own_raft_bare` (decisions.md), touched one shared file additively and
  ten `send` call sites by two lines each; `own_raft_phys` and its 21
  spec files did not move.

- **End state**, from `etc/tcb-report.py --scope election` and the final
  sweep: every Hoare triple on the election path is `Qed` except
  `wp_raftLog__slice_at`, which ends `Admitted. (* Trusted *)` for "the log
  fits in memory" (its arithmetic and why no premise can carry it are in the
  file, STATUS, false-statements.md and decisions.md). Ten axioms remain,
  all on the declared trust boundary: `Logger` (3), `own_Storage`, the RNG
  and `math/big` (4, over `own_big_Int`), `slices.Sort`, and protobuf's
  `Entry.Size`. The 12 protocol axioms in `election_protocol.v` are
  untouched by design. The trust *contract* grew this pass, and every
  growth is written at the clause it lives on: `is_Storage` gained
  `Entries`, `Hbounded` (stable last index `< 2^61`), `Snapshot`;
  `is_initialized` gained `globalRand` with its mutex, three error globals
  and `is_new_error` for one of them; `rand` gained its `Reader`.

- **Process facts worth keeping.** Seventeen agent runs over two days,
  two rate-limit interruptions, and one shared checkout. What worked: an
  independent `-vok` re-run of every claimed result before its commit; a
  full-tree `-vok` sweep whenever more than one writer had touched the tree
  and none was left to say what state it was in (three sweeps, ~35 min
  each); one agent per shared-file reshape, run alone. What cost time:
  concurrent `.vos` rebuilds after `base.v`/`inv_*.v` edits (one agent lost
  ~4 h of wall clock to cascades), a `link_` file written before its
  `proof_` file, a `(*T)` inside a Rocq comment, and positional
  destructuring of predicates that grew.


## 2026-09-21 (later) — builds now report a per-file time, and vok stopped eating vo

Claude Opus 5 (background job), at Upamanyu's request: "future builds should
report a per-file build time (vok or vo), to keep track of build
bottlenecks." No Rocq, `uv`, pandas or pytest on the machine, so everything
below was verified against a stub `rocq` and the real `.timing.sqlite3`.

The timing machinery already existed and had three holes.

- **`vok` builds were recorded as `vo`, overwriting them.** `file_timings`
  was keyed on the filename alone with an `is_vos` flag, and
  `CoqcFilter.from_coqargs` only looked for `-vos` — so a `-vok` run landed
  in the `vo` row. Since the inner loop *is* `make <file>.vok`, the `vo`
  column in the committed workflow was a mix of the two and nothing could
  separate them. The table is now keyed on `(fname, mode)` with `mode` one of
  `vo`/`vos`/`vok`. `migrate_file_timings` rewrites an old database in place,
  idempotently and under `BEGIN IMMEDIATE` so concurrent `make -j` workers
  cannot race it; on a copy of the real database it preserved all 592 file
  rows and 2997 Qed rows and dropped its scratch table.

- **Nothing was reported during a build.** The times only reached a sqlite
  file that a separate script read. Each file now finishes with
  `ROCQ TIME   418.79s vo  new/proof/.../proof_raft__send.v` on stdout. The
  seconds field is fixed-width so `grep 'ROCQ TIME' log | sort -rn -k3` ranks
  a build with no database at all. `make TIMING_MIN=10` raises the threshold,
  `make TIMED=false` still bypasses the wrapper, and the Rocq-CI path
  (`TIMING` set) is untouched.

- **`timing-report.py` needed pandas, which is not installed** — the
  2026-09-19 sweep could only compile it, not run it. Rewritten on the
  standard library, same shape of output, plus `--mode {vo,vos,vok}` and a
  `--selftest`. `make timing-report` is the short way in. It reads the legacy
  schema too, so an unmigrated database still reports.

**Two things found on the way, both fixed.**

- **A failed compile overwrote a good timing.** `filter.done()` ran before
  `p.wait()` and recorded unconditionally, so the time taken to reach an
  error replaced the last successful build's number. Failed compiles are now
  neither recorded nor printed.

- **Goose's `ⁱᵐᵖˡ` names were being truncated.** `Classify`'s regexes became
  bytes patterns when the filter moved to reading output as bytes, and `\w`
  is ASCII-only in a bytes pattern — so `Definition minⁱᵐᵖˡ` was recorded as
  `min`, colliding with a real `min` in the same file under a primary key
  that silently replaces. `new/code/` has ~1560 such definitions. The
  identifier pattern now admits `[\x80-\xff]`. This was pre-existing and is
  *not* caused by the schema change; it corrupted `qed_timings`, not file
  times.

**`etc/test_coqc.py` runs again.** It had been dead since the bytes move: the
fixtures were `str` against bytes patterns, so five of six tests failed with
`TypeError`. Ported to bytes and extended to 15 tests covering mode
detection, the report line, the failed-compile path and the migration.
Rocq's `Chars i - j` offsets turn out to be *byte* offsets, which is what
makes the existing `contents[start:end]` slicing correct on a file with a `σ`
in it — checked against the fixture rather than assumed. Since pytest is not
a dependency, `./etc/rocqc.py --selftest` runs the same functions with a
30-line capsys shim, matching the `--selftest` convention the other `etc/`
scripts already follow. 15/15 pass, and `./etc/timing-report.py --selftest`
is 12/12.

**Also corrected:** `STATUS.md` still listed the 64 `ruff check` errors under
"Known broken". They were fixed on 2026-09-19. `ruff check .` and `ruff
format --check .` are clean over 42 files, including everything touched here.

**What the real database says now**, for whoever picks up the election work:
the `vo` build of the election proofs is 5313s over 101 files, only 10% of it
in `Qed`. The top four are `proof_raftLog__slice.v` (605s),
`proof_raft__send.v` (419s), `proof_raft__campaign.v` (390s) and
`proof_raft__reset.v` (220s). `slice.v` reports 605s with **0s** of Qed time,
which is worth a look — the cost is all elaboration, not proof checking.
Treat these four numbers as `vo`-or-`vok`, per the conflation above; the
first clean build after this commit will say which.

---

## 2026-09-21 — audit: what `tcb-report.py` does not establish about the election claim

Claude Opus 5 (background job), branch `worktree-tcb-report-audit` off
`main`. Read-only against branch `worktree-election-close-admits` at
`0b3943d1f`, which claims *"every Hoare triple on the election path is Qed
except `wp_raftLog__slice_at`"* and cites `etc/tcb-report.py --scope
election` as the evidence. Nothing on that branch was touched.

**The claim is true of the source text and the tool reports it accurately.**
A comment-stripped scan written independently of the tool agrees with it
exactly over the 330 files of `v3_proof/election/`: 1 `Admitted`, 10
`Axiom`, 169 `Qed`, 78 `Parameter` (all in `Module Type`s), 0 `Abort`. Three
things the tool does *not* check also hold: all 330 files are in the
`Require` closure of `election.v`, which `should_build.v:51` requires; there
are no soundness escape hatches anywhere under
`new/proof/go_etcd_io/raft/` (no `Unset Guard/Positivity/Universe Checking`,
no `bypass_check`, no admitted `Program` obligations);
`check-module-discipline.py --scope election` exits 0, its two warnings
being the `Entry.Size` and `big.Int.Int64` axioms, which is expected.

**It does not follow that the tool demonstrates the claim.** Seven gaps,
written up with the plan in the new [tcb-accounting.md](tcb-accounting.md).
The three that change how the result should be read:

- **It never compiles.** No `subprocess`, no `rocq`, no `.vo`/`.vok`
  anywhere in `tcb-report.py` or `rocqscan.py`. A `Qed.` in a file that does
  not typecheck counts as a proof. The tree has 333 `.vos` and no `.vo`;
  `.vos` skips proof bodies by construction. The real evidence is a manual
  `-vok` sweep reported in a commit message, uncommitted, not tied to a
  revision. CI would be ground truth but fires only on `main` and PRs to it.
- **`--scope` is a path filter** (`tcb-report.py:515-524`), applied after the
  analysis. Every `election/` file requires `election_protocol.v` through
  `defs.v`, and its **12 axioms do not appear** in the scoped report, which
  prints `assumed 11`. The honest figure for the election development is 23.
- **The payoff theorem is out of scope and currently vacuous.**
  `raft_election_safety` lives in `election.v`, so `--view surface` under
  the scope reports only `wp_raft__Step_body`. And `election_protocol.v` has
  no allocation axiom for `own_raft_ghost`: taking
  `own_raft_ghost := λ _ _ _, False` and `is_leader := λ _ _ _, False`
  satisfies all twelve axioms, making both the corollary and `Step`'s triple
  trivial. This is next step #4 in STATUS and is not new — what is new is
  that **no output of the tool would lead a reader to it.**

Also: the surviving admission is filed more gently than it deserves. The
tool prints `wp_raftLog__slice_at` as *"trusted — deliberate"*, next to the
two `readonly.v` overflow assumptions, while
`proof_raftLog__slice.v`'s own header says the triple *"as stated is **false**
at a log with ~2^63 unstable entries"*. And what enters the trust base is the
whole triple, not the one admitted side condition at line 233 — the
distinction the `(* Trusted *)` marker cannot carry.

**Plan**, in three slices, in [tcb-accounting.md](tcb-accounting.md). Slice 1
is an afternoon with no Rocq: make `--scope` a dependency cone, flag
abstract predicates that nothing ever allocates, check reachability from
`should_build.v`, and replace `(* Trusted *)` with a parsed marker that
separates "assumed true" from "known false outside a stated regime". Slice 2
is what makes the tool definitive: join against a committed `-vok` manifest
keyed on git blob hashes, and diff the syntactic estimate against a real
`Print Assumptions` archived by CI — which is nearly free, since CI already
does the `.vo` build. Slice 3 gives `new/golang/defn/` its own line, because
this branch edits the operational model (`defn/map.v`) and no invocation of
the tool in the notes covers it.

**Nothing was changed in the tool or the proofs.** The audit is the
deliverable; the plan is unclaimed.

---

## 2026-09-21 (later) — election safety is not the payoff; the result is verified function specs

Claude Opus 5 (background job), same branch `worktree-tcb-report-audit`.
Correcting a framing the notes, the two protocol `.v` files and the earlier
entry above all shared, at Upamanyu's direction.

**The point.** This development verifies *code*. The result is a Hoare
triple on each function an etcd caller calls — `raft.Step`, and the `node`
interface above it. `raft_election_safety` is an **internal lemma**: a
sanity check that `nstate.t` and `step` entail the property raft exists to
provide, and so were not defined into triviality. Delete the corollary and
no claim about etcd's code is weaker; delete `wp_raft__Step` and there is
nothing left. Protocol-level theorems are in service of the function specs,
not the other way round.

This answers what `STATUS.md` had carried as open next step #5 ("decide what
the top-level Raft correctness statement should be"), so that item is now a
pointer to the new decision record rather than a question.

**Changed** — comments and prose only, no proof text:

- `notes/decisions.md` — new record at the end, with the five consequences.
  Also one stale phrase at the old scope decision ("supports the same payoff
  theorem" → "election-safety check").
- `notes/STATUS.md` — next step #5 answered; next step #4 now says what is
  actually at stake (the exported `wp_raft__Step` is vacuous, not merely the
  corollary); the trust-base sentence reworded to name `wp_raft__Step`.
- `notes/raft-election-refinement.md`, `notes/raft-proof-map.md` — both
  called it the payoff; both now say sanity check and point at the decision.
- `notes/tcb-accounting.md` — **G3 was wrong and is rewritten.** It had
  faulted `tcb-report.py` for not surfacing `raft_election_safety`. Under
  the correct framing the tool is right: the exported result of the election
  development *is* `wp_raft__Step_body`, and a theorem nothing calls is a
  leaf. The real gap is unchanged and sharper — that exported triple is
  vacuous under the trivial ghost model and no output says so. The Slice 2
  `Print Assumptions` item now names the function specs as what ground truth
  must be taken at.
- `v3_proof/election.v` and `v3_proof/election_protocol.v` — the three
  header comments that said "payoff". Verified comment-only: delimiters and
  string quotes balance, and both diffs sit entirely inside `(** … *)`
  blocks. The `election.v` block is byte-identical on
  `worktree-election-close-admits`, which does not touch it, so this merges
  cleanly into the in-flight branch.

**Not changed:** `election_protocol.v`'s scope note that "the point of the
model is election safety" was reworded, but no axiom, definition or proof
moved. Nothing needs re-checking.

---

## 2026-09-22 — the audit is two commands: `make`, then `tcb-report.py`

Claude Opus 5 (background job), branch `worktree-tcb-report-audit`, at
Upamanyu's direction. Process decision, and a rewrite of the plan that was
written under the wrong premise.

**The process.** An audit runs `make` first — `make ci`, or a narrower `.vo`
target — and then `etc/tcb-report.py` separately. `make` is the only thing
that checks proofs. `tcb-report.py`'s entire job is to check what the build
cannot, which is why it does not and should not invoke Rocq.

Writing the division out made the two tools' jobs much clearer than the
audit had them:

- **`make` establishes** that every `Qed` is real, that a functor really
  discharges its signature's `Parameter`s, and — with an `assumptions.v` —
  the exact transitive assumption set of a named theorem, seeing through
  `Notation`s and typeclass instances.
- **`tcb-report.py` establishes** whether the *statements* say what was
  meant (the definitions half of the TCB, the larger one), whether an axiom
  set has a non-trivial model, what is outside the build entirely, whether
  an `Axiom` is a declared boundary or unfinished work, whether an admission
  is a whole lemma or one side condition, and whether `new/golang/defn/` has
  moved.

**The insight this produced, which the audit had underweighted:** `make` is
necessary *and silently incomplete*. It checks exactly what
`should_build.v` reaches and says nothing about what it did not build, so a
`link_*.v` dropped from `election.v` removes a collection from the build
with no error anywhere. G6 (reachability) was filed sixth because it was
found sixth; under this process it is **first in importance** — the one way
a green build and a clean report can both be true of a development that is
not being checked. It is now plan item 2, marked "do this first if only one
thing gets done".

**What changed in [tcb-accounting.md](tcb-accounting.md):**

- new "The audit process" section with the two commands and the
  division-of-labour table;
- **G1 rewritten.** "The tool never compiles anything" was a criticism of
  correct behaviour. The real defect is narrower: the output does not say it
  assumes a green build, and the number was quoted as if it were proof
  evidence. Fix is a header line, not a compiler;
- G6 promoted with its reasoning; G7's fix is now the `Print Assumptions`
  reconciliation rather than "subsumed by G1";
- the plan is re-ordered and **one item is deleted**: the committed `-vok`
  manifest for the tool to join against. That was step 1's job restated
  inside a source scanner. If build provenance ever needs recording it
  belongs beside the build, as a CI artefact. Recorded in the file as
  "deliberately dropped", with why, so nobody re-proposes it;
- the `Print Assumptions` item is reframed as a **two-way reconciliation** —
  a name Rocq lists that the scanner missed means the printed TCB was too
  small; an `Axiom` in the tree Rocq does *not* list is dead, or the theorem
  does not rest on what everyone assumes. Neither direction is visible to
  either tool alone, which is what makes it step 2's work and not step 1's.

Also: `STATUS.md`'s tcb-report block now leads with the two commands,
`CLAUDE.md`'s Building section gained a short paragraph so a fresh agent
meets the process before it meets the numbers, and `STATUS.md` is dated
2026-09-22.

**No proof or tool code changed** — this is the plan, not its
implementation. Items 1–5 of Slice 1 need no Rocq and are unclaimed.

---

## 2026-09-22 (later) — G1 mostly dissolved; the gap list is reordered

Claude Opus 5 (background job), same branch. Upamanyu asked whether G1 in
[tcb-accounting.md](tcb-accounting.md) still makes sense under the two-step
process. Mostly it does not, and the file now says so rather than quietly
keeping a gap that had lost its reason.

**What G1 was, and what happened to its three parts:**

- *"The tool never compiles anything."* **Retired.** That is the design and
  it is right — step 1 checks proofs, and a source scanner that also tried
  would be a worse `make`. Criticising it was criticising the tool for not
  being a different tool. Stated in the file so nobody re-files it.
- *"The election branch's number was not backed by a build."* **Not a tool
  gap at all** — a fact about how that branch was audited. Moved up beside
  the other findings about it, as "What was not reproduced: step 1", which
  is where a reader looking for the branch's status will find it.
- *"A run carries no record of what it looked at."* **Survives, narrowed.**
  `tcb-report.py` prints counts with no revision, so the two halves of an
  audit cannot be shown to be about the same tree and a figure pasted into a
  commit message is unattributable a week later. Real, but output hygiene
  rather than a TCB check.

So G1 is now **the least severe of the seven**, and its plan item moved from
first to last in Slice 1 — where it was contradicting the G6 item beside it,
which said "do this first" while sitting at number 2.

**Also fixed: the list said "worst first" and was not.** It is discovery
order, and after two days of reframing the two orders had come apart. The
heading now says so and gives the real one — **G6, G3, G2, G4, G5, G7,
G1** — and the plan follows it. The labels themselves stay put: they are
cited in this journal and in commit messages, so renumbering would cost more
than the tidiness is worth.

Nothing else changed; no proof or tool code has been touched on this branch.

---

## 2026-09-22 (later still) — G2 and G6 are one bug, and get one fix

Claude Opus 5 (background job), same branch. Upamanyu, on being told how
plan items 1 and 3 differed: *"So the goal is to make sure the set of files
that are scanned by tcb-report are the same set of files built by make?
Make that just one feature."* Yes, and it is a better design than either
item was.

**The root cause the two write-ups had missed.** `tcb-report.py` decides
what to look at by **globbing a directory**; `make` decides by **walking a
dependency graph**. Every discrepancy between them follows from that one
difference — files on disk the build never compiles (G6), and files the
build compiles that a scoped report drops (G2). Found a day apart, written
up as two gaps, and only visible as one thing once someone asked what
separated the fixes. The gaps stay numbered separately, since the symptoms
are distinct and the labels are cited; the plan now has **one item** for
both.

**Plan item 1 is now "scan what `make` builds, not what a directory
holds"**: the scanned set becomes a dependency closure rooted at
`new/should_build.v`, or at the scope's aggregator under `--scope`. Both old
behaviours fall out — an orphan is excluded *and reported* (excluding it
silently would make an orphan look like the numbers improving), and a scoped
report automatically reaches `election_protocol.v`, so `--scope election`
prints `assumed 23` rather than `11`. `--scope-dir` survives as the old path
filter, labelled as not being the build's view.

**One implementation note that matters more than it looks.** Take the graph
from **`.rocqdeps.d`** — `rocq dep` output, which is what `make` actually
expands its prerequisites from (`Makefile:47-53` generates and includes it;
`Makefile:64` makes every `.vo` depend on it) — and not from a fresh
`Require` parse. A second parser is precisely how the two sets drift apart
again, which is the thing being fixed. It is generated rather than
committed, so the fallback to `rocqscan.requires` has to say in the output
that it is a guess at the build graph rather than the build's own answer.

Slice 1 is four items now (was five): the merged one, then G3, G4, G1.
Later items renumbered 5 and 6; every cross-reference in the file checked.

---

## 2026-09-22 — tcb-report scans the build graph; readonly.v is unbuilt; the election proof moves out

Claude Opus 5 / 5.5 (background job), branch `worktree-tcb-report-audit`.
Written after the branch was **rebased onto `main`** once
`worktree-election-close-admits` had landed there; the numbers below are for
that tree.

**Slice 1 item 1 of [tcb-accounting.md](tcb-accounting.md) is
implemented.** `etc/tcb-report.py` no longer decides what to look at by
globbing a directory: the scanned set is a dependency closure, rooted at
`new/should_build.v`, or at a scope's aggregator under `--scope`, so it is
the set `make` compiles. It reads `.rocqdeps.d` when present and says which
graph it used. Logical paths now resolve through `_RocqProject` — the old
longest-suffix match could not tell `New.code…raft.v3` from
`New.proof…raft.v3` and invented an edge from `base.v` to `v3.v`.

**It immediately found that `v3_proof/readonly.v` is built by nothing** —
955 lines, 5 `Admitted`, 7 `Axiom`, required by no file under any spelling
(confirmed by grep). `make ci` has never compiled it. `STATUS.md` next step
#8 had been proposing work on its loose triples for days. This is the
failure G6 was written about, found the first time anything looked.

**On `main`'s tree, `--scope election_proof` now reports assumed 23** — 1
`Admitted`, 22 `Axiom` — across 333 files. That is exactly the honest figure
the 2026-09-21 audit computed by hand, when the path-filtered `--scope
election` printed 11 by dropping `election_protocol.v`'s twelve. The whole
tree: 335 of 336 files in the build, `readonly.v` the one outside it.

**The election proof moved to `raft/election_proof/`**, a sibling of
`v3_proof/`, flattened, aggregator inside, at Upamanyu's direction. Layout,
reasons and costs are in [decisions.md](decisions.md). 332 files, 709
reference lines.

**How the rebase handled the move, which is the part worth knowing.** The
move was first made on the pre-merge `main` (184 election files). By the time
of the rebase `main` had 330 — 140 new, and a second helper directory,
`proof_MajorityConfig__VoteResult_helpers/`. Replaying the original rename
commit would have moved the old 184 and stranded the new 140 with dangling
`Require` paths. So that one commit was **regenerated** instead: the other
nine commits were cherry-picked onto `main` (conflicts only in append-only
files and one "Last updated" date), and the move and rewrite scripts were
re-run on the real tree. The move script now takes every `.v` file and every
subdirectory, which is what caught the second helper directory the original
hard-coded list would have missed. `journal.md` is excluded from the rewrite
from the start, since its dated entries record the paths as they were.

Static verification: 703 in-tree require targets all resolve except the two
pre-existing `should_build.v` parse gaps; nothing outside this file names
the old paths; both self-tests pass; `check-module-discipline --scope
election_proof` exits 0; both ruff jobs clean. **Build owed on this tree**
— the build recorded in the next entry was of the pre-rebase tree.
955 lines, 5 `Admitted`, 7 `Axiom`. It requires `v3_proof/protocol.v`; no
file in the repository requires *it*, under any spelling — confirmed by
grep, independently of the tool. `make ci` has never compiled it, so its
`Qed`s have never been checked by anything, and this section of `STATUS.md`
opened by asserting that the directory was built.

Worth noting for calibration: `STATUS.md` next step #8 had been proposing
for days that its eleven loose triples be brought into the module
discipline. Nobody had noticed the file was not in the build. **This is the
failure G6 was written about, found the first time anything looked.**

Also recorded: without `.rocqdeps.d` the fallback can *miss* an edge, since
`rocqscan.requires` models `From X Require a b` as concatenation where Rocq
does a prefix-filtered suffix match, and misses an `Import` that lands on
the next line. `should_build.v` has two requires it cannot resolve for those
reasons. So a false orphan is possible in principle — not here, where
nothing names `readonly` at all. Fix the parser, and better, run `make` once
so the build's own graph exists.

### The election proof moved to `raft/election_proof/`

At Upamanyu's direction, and because the previous finding made the point
that `v3_proof/` was two unrelated developments sharing a directory: the
election work is now a **sibling** of `v3_proof/`, flattened, with its
aggregator inside it. `v3_proof/` keeps `base.v` (shared), `protocol.v` and
`readonly.v`. Layout, the alternatives and the costs are in
[decisions.md](decisions.md).

~190 files moved, 451 lines of references rewritten across `.v`, `.md` and
`etc/*.py`. Two things about how it was checked:

- **There is no Rocq on this box, so the move is statically verified, not
  compiled.** Every `Require` in the raft tree resolves through
  `_RocqProject` to a file that exists (429 require targets, 0 unresolvable
  except the two pre-existing `should_build.v` cases); nothing mentions the
  old paths; `check-module-discipline.py --scope election_proof` exits 0;
  both self-tests pass. **A build is owed** — `make -j8 TIMED=false
  new/proof/go_etcd_io/raft/election_proof/election.required_vos`.
- `notes/journal.md` was deliberately **excluded** from the reference
  rewrite. It is append-only, and its dated entries are records of what the
  paths were at the time. Everything else — STATUS, decisions, gotchas,
  raft-proof-map, raft-election-refinement, tcb-accounting, CONTRIBUTING,
  `bugs/` — was updated, including `--scope election` → `--scope
  election_proof` in every command example.

**Left for whoever picks this up:** run the build. Then Slice 1 items 2-4
(never-allocated predicates, admission markers, run attribution), which are
unclaimed and need no Rocq. And decide `readonly.v`'s fate: require it from
`should_build.v` and find out whether it still compiles, or retire it
deliberately.

---

## 2026-09-22 (evening) — the build: raft tree green at `.vok`, readonly.v included

Claude Opus 5.5 (background job), branch `worktree-tcb-report-audit` at
`21b678d3b`. Upamanyu asked for a build after the `election_proof/` move,
which had been recorded as statically verified only.

**Rocq was on the box all along** — `~/.opam/perennial/bin/rocq`, 9.4+alpha
— just not on this shell's `PATH`. The earlier entry and the decision record
said otherwise; the record is corrected, and gotchas.md now says how to
find it.

**What was run, and why not `make ci`.** Nothing anywhere had `.vo` files, so
`make ci` would have meant a full `.vo` build of Perennial from scratch —
hours on this box, with a `rocqworker` belonging to another session holding
5.4 GB of the 15. Instead, the documented vos/vok route, in three phases:

| phase | what | result |
|---|---|---|
| 1 | `.vos` closure of `election_proof/election.v` and `v3.v`, `-j4` | 459 files, **0 errors**, 8m16s, peak 1.2 GB |
| 2 | `.vok` of all 197 raft files the build reaches, `-j2` | 197 files, **0 errors**, 27m, peak 2.8 GB |
| 3 | `.vok` of `v3_proof/readonly.v`, an extra — nothing builds it | **0 errors**, 3m37s |

`-j2` in phase 2 because the `Step` helpers peak ~2.3 GB each and three at
once would have crowded the other session's worker. Phase 1 needed no
rebuilds in phase 2, so the `.vos` closure was complete.

**So:** the move is compiled, every proof body in the build checks, and
`readonly.v` is not broken — only unwired. What this is *not*: a `make ci`.
`-vok` skips universe-constraint checking (CONTRIBUTING.md), and the two
`should_build.v` lines `rocqscan` cannot parse are off the raft path and
were not exercised.

**A scare worth recording, because it would have been easy to misread.**
Phase 2 ended with `make` exit 0 and **zero `.vok` files on disk**. Rather
than report either way, two direct tests: the exact `%.vok` invocation on a
small file writes no `.vok` with or without `-o` (Rocq 9.4+alpha simply does
not emit the marker), and a negative control — a file whose only `Qed`
proves `False` — *fails* under the same flags while a true one passes. So
the checking is real and the missing markers are a toolchain change. In
gotchas.md, with the consequence that `make` can never treat a `.vok` target
as up to date.

**`.rocqdeps.d` now exists here**, so `etc/tcb-report.py` used the build's
own graph for the first time. It agrees exactly with the fallback parser:
197 files in the build, `readonly.v` the single orphan, a 195-file cone for
`--scope election_proof`. That is also the first test of the `.rocqdeps.d`
parser on real `rocq dep` output.

Also found and verified: `etc/mkvok` matches nothing — it greps `make -n`
for `echo "COQC`, and the Makefile prints `ROCQ COMPILE` (253 such lines for
one target, 0 matches). In gotchas.md.

**Left:** decide whether `readonly.v` is wired into `should_build.v` (it
would pass) or retired. A real `make ci` is still the only thing that checks
universes and the rest of `should_build.v`. Slice 1 items 2-4 remain
unclaimed.

---

## 2026-09-22 (late) — readonly.v wired into should_build.v, as a stopgap

Claude Opus 5.5 (background job), same branch. At Upamanyu's direction:
`new/should_build.v:51` now requires `go_etcd_io.raft.v3_proof.readonly`,
"for now" — the old proofs are due a larger clean-up later, and until then
it is better checked than silently skipped.

Verified through the build's own graph: after regenerating `.rocqdeps.d`,
`rocq dep` records the new edge, and `etc/tcb-report.py` reports 198 files
in the build (was 197) and **no file outside it**. The whole-tree assumed
count rises from 33 to 45 — `readonly.v`'s 5 `Admitted` and 7 `Axiom`, which
were always there and are now counted because they are now built. Not
recompiled: `readonly.v` is unchanged and passed `-vok` an hour earlier, and
the edit is one `Require` line. A `make ci` would compile `should_build.v`
itself; nothing here has.

The inserted line moved `election.v`'s entry from line 51 to 52; the three
notes that cited it were corrected.

---

## 2026-09-22 (night) — rebased onto main; the merged election work builds green at `.vok`

Claude Opus 5.5 (background job). Upamanyu asked for a rebase on `main`,
which had meanwhile taken `worktree-election-close-admits` (17 commits, the
election path closed modulo one admission) and a build-timing change.

**How it was done.** Nine of the ten commits were cherry-picked onto `main`;
their conflicts were all in append-only notes (`journal.md`, `decisions.md`,
`gotchas.md` — keep both, `main`'s first), one "Last updated" date, and one
`decisions.md` paragraph where the corrected text won. The tenth — the move
to `election_proof/` — was **regenerated** rather than replayed, because
`main` had 140 election files the original rename had never seen; the
previous entry has the details. The pre-rebase branch is kept locally as
`backup/tcb-report-audit-pre-rebase`; the rebased one was pushed as
`worktree-tcb-report-audit-rebased`, since replacing the original remote
branch needs a force-push, which is Upamanyu's call.

**Then built, because a regenerated move over 140 unseen files is not
something to leave unbuilt**, at `454e0d780`:

| phase | what | result |
|---|---|---|
| 1 | `.vos` closure of `election_proof/election.v` and `v3.v`, `-j4` | 471 files, **0 errors**, 9m44s |
| 2 | `.vok` of all 336 raft files — everything `should_build.v` reaches | 336 files, **0 errors**, 58m, peak 3.0 GB |

This is the first reproducible build of the merged election work: the
2026-09-21 audit's complaint was that its only evidence was a `-vok` sweep
reported in a commit message. It still is not a `make ci` — `-vok` skips
universe constraints — but it is a build at a named revision, re-runnable
from the repository.

`tcb-report.py`, now reading the regenerated `.rocqdeps.d`: **336 files in
the build, none outside it**; the whole raft tree assumes 43 (8 `Admitted`,
35 `Axiom`), and `--scope election_proof` 23 (1 and 22). The 43 is the same
whole-tree figure the audit quoted for the election branch, now that
`readonly.v`'s 12 are built and counted rather than merely present.

The 3 gotchas from the earlier build still hold on `main`: its Makefile
change only split the timing database by mode ("vok overwriting vo" meant
timing rows), and left the `%.vok` rule alone.

---

## 2026-09-22 — The election protocol's ghost state is constructed, not assumed

Claude Opus 5 (background job), at Upamanyu's request: "prove all the axioms
in `election_protocol.v`; keep going until that proof is admit-free". Branch
`election-protocol-ghost`, off `main` at `a821f4e1a`.

- **Did:** `new/proof/go_etcd_io/raft/v3_proof/election_protocol.v` has no
  `Axiom` and no `Admitted`. The twelve ghost-state axioms — `own_raft_ghost`,
  `is_message`, `is_leader`, `raft_election_names`, the two instances, the
  two typeclass facts, `own_raft_ghost_excl`, `own_raft_ghost_step`,
  `own_raft_ghost_outbox`, `own_raft_ghost_is_leader`, `is_leader_unique` —
  are now definitions and `Qed` lemmas, plus an `own_raft_ghost_alloc` that
  was not asked for and is the point of the exercise (see below).
  `etc/tcb-report.py` over the whole raft proof drops from 43 assumed to
  **31** (8 `Admitted`, 23 `Axiom`), and `election_protocol.v` is no longer
  in its "Incomplete" list at all.

### The construction

The shape the old comment predicted — "authoritative map of node states + a
set of sent messages, tied together by an invariant" — is not what this is.
There is **no Iris invariant**, and that is load-bearing:
`own_raft_ghost_outbox` is stated as a plain entailment, not a fancy update,
so it cannot open one. Everything is node-local instead.

`raft_election_names` became a record: `re_cfg : gset w64` and
`re_votes : gmap w64 gname`, one ghost map per node holding `term ↦ candidate`.
`is_vote γ v term cand` is a frozen entry in `v`'s map — persistent because
frozen, unforgeable because allocating one takes `v`'s `ghost_map_auth`, which
lives exclusively inside `own_raft_ghost γ v _`. `is_message` is then defined
by cases: a `VoteResp` with `reject = false` carries the vote it reports,
every other message carries nothing. `is_leader γ id term` is a quorum of
`is_vote`s, so `is_leader_unique` is `quorums_intersect` (the same lemma and
the same `is_quorum` as `readonly.v`; copied rather than shared, since
`election_protocol.v` does not depend on `readonly.v`) plus the agreement of
two `is_vote`s. No leader registry.

The invariant that makes it work is `vote_hist_ok voted s`: every term in the
history is `≤ s.(nstate.term)`, and at the current term the history agrees
with `s.(nstate.vote)` — absent exactly when the vote is `W64 0`. Since every
rule that clears `nstate.vote` also raises `nstate.term` past everything in
the history, a node cannot vote twice in one term. `own_raft_ghost_step` is
one induction over `step`; only `step_campaign` and `step_grant_vote`
allocate. Details in
[raft-election-refinement.md](raft-election-refinement.md).

### Three things the interface got wrong, all found by trying to prove it

This is the fourth time on this project that writing the proof has shown a
statement to be **false of what it describes** (after `appendEmptyEntry`,
`step_win` and `maybeSendSnapshot`'s precondition). Each of the three is a
way of electing two leaders in one term.

1. **`own_raft_ghost_step` quantified over `cfg`.** `step cfg id s recv s'`
   with `cfg` free at each use means a caller can pick `cfg := {[id]}`, in
   which the node is its own quorum, campaign, record its own self-addressed
   `VoteResp` and win — twice, for two different nodes, in the same term.
   `is_leader_unique` is then not provable, and with an allocation lemma the
   axiom set would be outright inconsistent. `cfg` now lives in `γ`, and
   `own_raft_ghost_step` reads `step γ.(re_cfg) id s recv s'`.
   `wp_raft__Step_body` carries a new `γ.(re_cfg) = cfg` premise tying it to
   `own_raft_phys`'s `cfg`; `proof_raft__Step.v` opens with `subst cfg`.
2. **`step_campaign` had no no-wrap premise**, so `word.add s.term 1` could
   wrap round to a term the node had already voted in. Now
   `uint.Z s.(nstate.term) + 1 < 2 ^ 64`. Free at the one construction site:
   `wp_raft__hup_body` has carried that premise since `send`'s zero-term
   panic was pinned down, so `apply step_campaign; done` still works
   unchanged.
3. **`step_grant_vote` could grant to `W64 0`**, which is the Go code's
   `None` — so "voted for nobody" and "voted for node 0" are the same state,
   and a node could grant to `0` and then grant again to somebody else in the
   same term. Now `m.(msg.from) ≠ W64 0`. Also free:
   `wp_raft__Step_body` already requires `From ≠ 0` of a `MsgVote`, and all
   three sites discharge the new goal by `done`.

`own_raft_ghost` also carries `id ≠ W64 0`. A node whose own id is `None`
would record "voted for `0`" when it votes for itself in `become_candidate`,
which `vote_hist_ok` reads as "did not vote". It is a property of the node,
so it belongs in the predicate rather than in a rule; `own_raft_ghost_alloc`
takes `W64 0 ∉ ids`.

### Why there is an allocation lemma

None of the twelve axioms says the ghost state is inhabited, so
`own_raft_ghost := False` discharges all twelve. `own_raft_ghost_alloc` —
fresh `γ` for any finite set of nonzero node ids, each in the initial state —
is what makes the other eleven mean something. It is the only lemma here
nothing else uses, and it should not be deleted for that reason.

### What it cost, and what was slow

About 20 rocq iterations on `election_protocol.v`, at **3–5 s each**: the
file sits directly on `proof_prelude` and nothing else, so `make <file>.vok`
is a genuinely fast loop and rocq-warm was never needed for it. The
expensive part was the sweep afterwards, not the proof.

The tactic failures were all the usual Iris ones, and two are worth
recording; both are in [gotchas.md](gotchas.md) now:

- **`rewrite decide_False` picks the outer `decide`.** `become_follower`'s
  vote field is `if decide (term = s.term) then s.vote else W64 0`, and
  `vote_hist_ok` wraps *that* in `if decide (… = W64 0)`. The rewrite matches
  outermost-leftmost, so it takes the wrapper and leaves an unprovable side
  condition. Fixed with two one-line lemmas
  (`become_follower_vote_ne`/`_same`) that rewrite the projection before
  anything unfolds it.
- **`/=` eats `[x] ++ l`.** `rewrite /send_msgs /=` turns the outbox into
  `outbox ++ (m :: ms)`, so the second `big_sepL_app` of the pair has nothing
  to match and you need `big_sepL_cons`.

Two more, cheaper: `Forall_forall` resolves to Rocq's `List` version (with
`In`, not `∈`) — use `Forall_lookup_1`; and `iDestruct (big_sepL_singleton
with "H")` leaves `P ∗ emp` rather than `P`, which then fails to instantiate
a wand — destruct `"[$H _]"` instead.

### Evidence

`-vok` (the authoritative check; `.vos` skips `Qed`) exits 0 on
`election_protocol.v` and on a sweep of every proof-bearing file in the
election development. `etc/check-module-discipline.py --scope election` is
clean (5 pre-existing notes/warnings, none new).

### Also: rocq-warm notes refreshed against `11b27cb`

Re-read `upamanyus/rocq-warm` (checked out at `~/rocq-warm`) and brought
`gotchas.md` and `STATUS.md` up to date. Two things changed since the
2026-09-16 entry, both from 2026-09-18:

- **A client going away stops the work but keeps the session**, parked at the
  line Rocq reached; the next check replays from there. Exit 130, which is
  **not a verdict** — like exit 2, it says the question was withdrawn, not
  that the proof is good or bad. This obsoletes the advice in the 2026-09-16
  entry that killing a client wedges that file as busy until the half-hour
  wall timeout; the slot now comes back in the couple of seconds the
  interrupt takes.
- A cold check used to spawn **two** `rocq repl` and kill the first, so every
  file's first check paid two startups and the recorded pid was a dead one.
  One now.

And one thing that was always true but matters more now that this project
works in worktrees: rocq-warm keys its daemon on `git rev-parse
--show-toplevel`, which **in a worktree is the worktree**. So agents in
separate worktrees do not share a session table or a memory budget, and the
"sessions evict each other" entry in gotchas.md only applies within one
checkout. They still share `MemAvailable`, which eviction watches.
`--compile` and `--rebuild` (build the `.vo`s from the check) are also
documented now; neither is what this `vos`-only tree wants day to day.

---

## 2026-09-22 (later) — Audit: what the election proof does *not* cover

A subagent (Fable) was asked one narrow question: considering **safety only**,
is leader election fully verified — are all safety bugs in `raft.go`, for the
no-reconfiguration no-proposals case, precluded? Answer: **no**. The gaps
below are its findings; the two marked *(verified here)* I re-checked against
the sources myself, the rest are its citations and are worth spot-checking
before anyone leans on them.

Ranked by safety weight:

1. **No crash or persistence model, at all.** `Step` is a `wp`, not a `wpc`;
   `HardState`, `hardState()` and `loadState` (`v3.v:5302,5304`) appear in no
   spec; `own_raft_ghost` is volatile. The Go ordering that makes a vote
   durable before the `MsgVoteResp` leaves (`msgsAfterAppend` →
   `MsgStorageAppend.Responses`) is invisible here, because
   `own_raft_phys` folds `msgs` and `msgsAfterAppend` into one abstract
   outbox and `step_drain` lets any submultiset go at any time. So the
   canonical election-safety bug — vote, crash before it is durable,
   restart, vote for someone else — is outside the proof, and so is the
   weaker bug of routing a granting `MsgVoteResp` through `r.msgs`.
2. **`own_raft_phys` has no constructor.** There is no `newRaft` spec and no
   `is_Storage` instance (no `MemoryStorage`), so its satisfiability is by
   inspection only — and this predicate was provably `False` once before
   (the duplicated `trk` ownership, fixed 2026-09-14). Until something
   builds one, every triple in the development could in principle be vacuous.
   `own_raft_ghost` *is* now known inhabited (`own_raft_ghost_alloc`), which
   is the asymmetry worth closing next.
3. **`Step` is specified only for `MsgHup`/`MsgVote`/`MsgVoteResp`.** The
   model's `step_higher_term` with `from_leader = true` — receiving an
   `App`/`Heartbeat` at a higher term, stepping down *and adopting the
   sender as leader* — has no collection refining it. Nor does
   `stepCandidate`'s step-down on an equal-term `MsgApp` (`v3.v:4644-4660`),
   `becomePreCandidate`, `stepFollower`'s `lead := m.From`
   (`v3.v:4753,4762,4771`), `MsgForgetLeader`, `tickElection`, or
   `Ready`/`acceptReady`/`Advance`. `step_drain` likewise refines nothing.
4. **The log is dropped, so `isUpToDate` is unconstrained.** Rejecting is
   always legal in the model, so a bug that makes a node *grant* to a stale
   candidate is a bug in `Step`'s `MsgVote` branch that this proof cannot
   see. Election Safety survives it (it does not depend on log currency);
   Leader Completeness and State Machine Safety are not expressible at all.
5. **`HnoConfChange` cannot be discharged by a real cluster** *(verified
   here)*. `inv_raftlog.v:139-140` requires
   `Forall (λ e, Type = EntryNormal) (sents ++ uents)` — the **whole** log —
   while `RawNode.Bootstrap` (`v3.v:391`) writes `EntryConfChange` entries at
   `v3.v:447`, and `StartNode` calls it. So `own_raft_phys` is false of every
   freshly bootstrapped etcd node until those entries are compacted away.
   Only "no conf change in `(applied, committed]`" is actually needed, so
   this is cheap to weaken, and it should be. This is the same shape as the
   four statements previously found false of the code, and is the nearest
   thing to a fifth.
6. **Scope premises that are not etcd's configuration.** `preVote = false`
   and `checkQuorum = false` (`inv_raft_phys.v:112-113`) — etcd's server
   turns both on by default. Also `Hnosnap` (no snapshot ever received,
   `inv_raftlog.v:139`), which is a scope assumption nothing had written
   down. The `To = id` / `Term ≠ 0` / `From ≠ 0` premises on incoming
   messages are assumptions about the transport and peers; Go checks none of
   them, and a `Term = 0` `MsgVoteResp` really does fall through to
   `stepCandidate` and get counted (`v3.v:3928`).

The remaining trust base does **not** look like it can hide an election-safety
bug: none of the ten axioms feeds a vote or leader decision, and the
`raftLog__slice` admission is an arithmetic bound on the
`hup → hasUnappliedConfChanges → slice → extend` path that cannot reach a
`Term`/`Vote` write. `protocol.v` and `readonly.v` are confirmed *not* on the
election path — nothing under `election/` requires them.

The audit found no fifth statement outright false of the code beyond item 5,
and its adversarial re-read of this morning's ghost construction came back
clean: `own_raft_ghost_alloc` is non-vacuous, `is_vote` is unforgeable,
`is_quorum` matches Go's `votedCnt >= len(c)/2+1`, `quorums_intersect` is
correct, and `become_*`/`can_vote`/`record_vote` match the Go bodies.

**Two corrections to the entry above, both mine.** The earlier entry and the
commit message for `7cb3d419d` say `proof_raft__Step.v` "opens with
`subst cfg`". It does not, and deliberately: `subst` removes the binder and
the branch lemmas are applied to `cfg` *by name*, which then resolves to
Perennial's global `cfg : language → Type`. The file asserts a copy of the
witness at `γ.(re_cfg)` instead and says so in a comment
(`proof_raft__Step.v:47-50`). And `STATUS.md`'s "election safety now rests on
nothing but the framework and the declared trust boundary" was true of the
code-free corollary and misleading about everything else; it has been
rewritten.

## 2026-09-22 (evening) — One `own_raft_phys`: the physical state split from the protocol state

Branch `raft-phys-one-predicate`, off `election-protocol-ghost`.

### How this started

The session began as "prove `newRaft`" (STATUS item 1, `own_raft_phys` has
no constructor). Surveying `newRaft`'s callees turned up three things
worth keeping, and then the user stopped the work: the approach being
taken -- adding `own_raft_phys_atQ`-style variants (a `becomeFollower` spec
on `own_raft_phys_at` because `newRaft`'s struct has a nil `r.step`; an
`own_raftLog_atQ Q` so that `committed`/`applied` survive `lastEntryID`) --
was the wrong path. The instruction, recorded in decisions.md ("Three
layers"): there should be no `own_raft_phys_at`; the step function belongs
in `nstate.t`; `nstate.t` is the most abstract description of the physical
state that lets every WP be stated on `own_raft_phys`; the ghost state may
take a different type, related by a relation; and the docs must say so.
Both variants were reverted before anything was built on them.

### Kept from the `newRaft` survey

- **`own_tracker` was unsatisfiable by any struct `newRaft` builds.** It
  required `Config.Learners ↦$ ∅` and `LearnersNext ↦$ ∅`; a map points-to
  implies a non-nil location (`own_map_not_nil`), and `MakeProgressTracker`
  writes `nil` to both, `Config.Clone` keeps `nil`, and only adding a
  learner allocates one. Fixed with `own_idset_opt` (nil, or owned) in
  `inv_tracker.v`. The second time `own_raft_phys` has been found `False`
  of reachable states.
- **`confchange.Restore` and `raftpb.ConfState.Equivalent` are not
  translated** (`confchange.v.toml` is `translate = ["Changer"]`;
  `raftpb` is types-only). `newRaft` calls both. Either translate
  `confchange` (Simple/apply/checkInvariants, voters-only case) or postulate
  `Restore`; `Equivalent`'s sort-and-`DeepEqual` is faithfully "pairwise
  permutations and equal `AutoLeave` ⇒ nil" (the Go `ConfState` has exactly
  the five modelled fields).
- `Storage.InitialState` is best a premise of `newRaft`'s spec (a triple
  about the specific storage), not a new `is_Storage` clause; and
  `validate`'s error paths are all dead under premises on the `Config`.

### What was done

- `election_protocol.v`: the record is now `pstate.t`, functions prefixed
  `p` (`psend_msgs`, `pbecome_follower`, `pbecome_candidate`,
  `pbecome_leader`, `pcan_vote`, `init_pstate`). No proof changed.
- `election/defs.v`: the **physical** `nstate.t` -- the six protocol fields
  plus `stepfn : func.t`, `progress : gmap w64 loc`, `log : loc`,
  `lent : option tracker.ProgressTracker.t` -- with `step_func_of`, the
  physical transitions (`send_msgs`, `reset_to`, `become_*`), `to_pstate`,
  `nstate_wf`, `nstate_rel`, and one commuting lemma per transition.
- `election/inv_raft_phys.v`: one `own_raft_phys`. `own_raft_phys_at`,
  `own_raft_bare`, `own_raft_notrk` and their split/join/intro lemmas are
  deleted. `own_raft_phys_intro` takes `r ↦ rv` first (see gotchas).
- Every spec on the election path restated on `own_raft_phys`, including
  five that were on raw struct pieces (`abortLeaderTransfer`,
  `resetRandomizedElectionTimeout`, `increaseUncommittedSize`, `promotable`,
  `hasUnappliedConfChanges`). `Visit`'s closure contract now carries the
  progress map. `Step` takes `nstate_rel s ps` and hands back
  `nstate_rel s' ps'`; its helpers take and return `nstate_wf`.

### Dead ends, in the order they were hit

1. **A loan of just the log page** (`lent : option (slice × dfrac × list
   Entry)`). Not enough: `appendEntry` needs the *whole* log held at a
   fixed split across `increaseUncommittedSize`.
2. **`log_lent : bool` without the tracker.** Not enough: handing the
   borrowed `Progress` back to the tracker before `send` and re-borrowing
   it by its key afterwards (which is what `nstate.progress` is for)
   yields `∃ pv iv`, and `SentEntries` needs the facts about `pv`/`iv`
   established before the send. So the loan covers the tracker too; that
   is `lent : option tracker.ProgressTracker.t`.
3. **Passing a `lent = None` premise positionally** fixes the callee's
   state from the premise's *type*, i.e. at the caller's `s`, even when
   the call is at `send_msgs s ms` or `become_leader id s1`; the frame then
   fails. Discharge it as a side goal instead
   (`wp_apply (lem with "[$Hphys]"); first exact Hlent.`).
4. **Giving `reset` its state explicitly** (`reset _ _ _ (s <| stepfn := … |>)`)
   ran 24 minutes and failed to frame; leaving it to the frame takes 14s.
5. **`simpl in *` on re-seal side goals** ran 12+ CPU-minutes per file:
   the struct carries `func.t` values and `simpl` unfolds `functions …`.
6. **rocq-warm replays against the dependency it loaded first** -- after
   reordering `own_raft_phys_intro`'s arguments, warm checks kept failing
   with the old order until `rocq-warm stop`.

### Evidence

- `make -k -j3` of the `.vok` target of every file in the election
  development (`election_protocol.v`, `election.v`, `election/*.v` and both
  `*_helpers/` directories): **exit 0, 332 files checked**, no errors. Every
  proof touched here was also checked cold with rocq-warm along the way.
- `etc/check-module-discipline.py --scope election`: the same 5
  notes/warnings as before, nothing new.
- `etc/tcb-report.py --scope election`: still **10 `Axiom`, 1 `Admitted`**;
  174 `Qed` lemmas (was 169); 44 definitions / 471 lines reached from the
  exported statements (was 38 / 428).

### Not done

`newRaft` itself. STATUS items 1 and 2 now say what it needs; item 2 (the
log's three shapes, and no `committed`/`applied`) is the same kind of fix
as this session's and should come first.

## 2026-09-23 — The trace hooks own nothing

Follow-up to the previous entry, same branch. The six `traceX` hooks
(`traceBecome{Follower,Candidate,Leader}`, `traceReceiveMessage`,
`traceSendMessage`, `traceReplicate`) were still specified on raw pieces:
five on `own_raft_misc`, `traceReplicate` on the entries slice. Yesterday's
entry left them alone because moving them onto `own_raft_phys` would have
cost a re-seal and a reopen at each of their 12 call sites, several inside
the `Step` helpers. That was the wrong comparison. Their translated bodies
are `do: #()`, so the honest triple owns nothing:
`{{{ is_pkg_init raft }}} … {{{ RET #(); True }}}`. They are stated that way
now, and callers write `wp_apply wp_traceX. try wp_auto.` One small trap:
`as "_"` fails against a `True` postcondition ("iIntro: nothing to
introduce"). decisions.md ("Three layers") is amended to match.

Evidence: `.vok` of all 332 election files, make exit 0; module discipline
and TCB unchanged (10 `Axiom`, 1 `Admitted`).

---

## 2026-09-23 — tcb-report separates Go-function triples from root lemmas

Claude Opus 5.5 (background job), branch `worktree-tcb-report-audit`
(pushed as `…-rebased`). Upamanyu noticed `raft_election_safety` in
`--view surface`'s "externally-facing results" and pointed out that it will
be an internal protocol lemma serving some WP, not a result.

**Why it was there.** `exported_surface` had two rules. Collections were
handled correctly — a spec nothing calls is a result — but any file outside
the collection layout that nothing in the proof root required had *every*
unused non-definition promoted, triple or not; its docstring called such a
theorem "the payoff". `should_build.v` is outside the proof root, so every
aggregator looked like a leaf. That rule put `raft_election_safety` on the
surface once `--scope` became a dependency cone, and `readonly.v`'s four
protocol facts once it was wired in.

**Now:** results are Go-function Hoare triples nothing else calls, however
they are written — a collection's `_body`, or a loose lemma like `v3.v`'s
`wp_Node__Propose` (checked through `follow_alias`). Everything else that
nothing uses is a **root lemma**: its own section, not a result, not counted
in the TCB and not seeding the definitions closure. An axiom or admit among
them is still counted under assumed, as before.

| | results | definitions | TCB |
|---|---|---|---|
| raft tree, before | 8 (+4 assumed) | 81 / 744 lines | 132 / 966 lines, 6.3% |
| raft tree, after | 4 (+3 assumed) | 79 / 735 lines | 126 / 937 lines, 6.1% |
| `--scope election_proof`, before | 2 | 53 / 605 lines | 78 / 689 lines |
| `--scope election_proof`, after | **1** (`wp_raft__Step_body`) | 53 / 605 lines | 77 / 684 lines |

Five root lemmas: `raft_election_safety`, and in `readonly.v`
`start_heartbeat`, `start_req_ctx`, `heartbeat_ack_quorum_not_stale` and
the assumed `is_committed_in_term_pers`. The election cone's definitions
do not move, since everything the corollary mentions is reached from
`Step`'s spec anyway.

**The section says "not the same as safe to delete", for a reason worked out
the same day** and recorded under consequence 1 of the 2026-09-21 decision:
`raft_election_safety` is the *only* user of `own_raft_ghost_is_leader` and
`is_leader_unique`, and without that pair the ghost state has a trivial,
allocatable model (a per-id token ignoring `s`, `is_message` := `True`).
Also found: `own_raft_ghost_excl` is used by nothing.

**Left open:** the five triples for *unexported* Go functions in
`readonly.v` (`wp_readOnly_*`, `sendMsgReadIndexresponse`,
`stepLeader_MsgReadIndex`) are still results. By the 2026-09-21 decision no
etcd caller can call them, so arguably they are not; making Go's export rule
decide rather than annotate is Upamanyu's call. (`wp_Node__Propose` carries
no Go tag either way: it calls `Propose` through the `Node` interface,
`#(methods n.(interface.ty) "Propose" …)`, which names no concrete Go
function to tag.)

Verified: self-test extended with a leaf file holding a loose triple and a
root lemma that is the only user of a definition; a mutant that promotes
every root back to a result fails four of its assertions. Both ruff jobs
clean; `check-module-discipline --scope election_proof` exits 0.

---

## 2026-09-23 (later) — tcb-report's summary table names its columns

Upamanyu could not tell what the `43` in `assumed  43  125 lines` counted —
fairly: the table had no header. It is **Rocq declarations** (one per
`Axiom`, `Admitted` lemma, `Definition`, `Record`, …; the `43` is 35
`Axiom` + 8 `Admitted`), and the second column is **source lines of those
statements, proofs excluded** (`rocqscan.py:362`). Every row uses the same
two units, so `TCB 126` is 43 + 4 + 79 declarations. The summary now prints
a `decls` / `stmt size` header and a two-line legend under the TCB row.

---

## 2026-09-23 (later still) — "of those, trusted" was the wrong label

Upamanyu asked what "of those, trusted" meant, given that everything in the
table counts toward the TCB. Right: the row was named after the
`(* Trusted *)` comment marker, not the TCB sense of trusted. By the
convention in STATUS.md an `Admitted` means in scope but unfinished, and the
marker picks out the admissions the development means to keep; all three
marked declarations are `Admitted`. The row now reads **"admits meant to
stay — marked (* Trusted *); the other 5 are unfinished"** (whole raft tree:
3 of 8; election cone: 1 of 1), `--view assumed` tags them "(meant to stay)",
and the marker's comment no longer claims "everything else is debt", which
was false of the 35 axioms.

Still true, and still G4: the marker cannot tell a benign modelling
assumption from `wp_raftLog__slice_at`, whose own header says the triple is
false at ~2^63 unstable entries. Nor does anything classify the axioms —
the keyword is supposed to say "outside the protocol", but 12 of the 35 are
the ghost-state axioms, which are owed work (STATUS next step #4).

---

## 2026-09-23 (evening) — the assumed breakdown: triples, undefined declarations, other

At Upamanyu's direction. The summary's breakdown of the assumed row is now
**Hoare triples about Go code / undefined declarations / other** (whole raft
tree 15 / 15 / 13 = 43), replacing "opaque declarations" and "properties of
the model" — the latter was a catch-all defined by exclusion, and none of
its members is about the protocol model; they are facts about the undefined
ghost predicates.

The "admits meant to stay" row is gone. It was a count along a different
axis — admits carrying a `(* Trusted *)` comment, all three of which are
also triples — printed among the three categories, so it read as a fourth
one that overlapped "Hoare triples about Go code". What matters in that
table is how many things are `Admitted` or axiomatized, which the assumed
row already says.

And the marker's meaning is corrected everywhere: `(* Trusted *)` means an
admission **signed off on for now**, not one "meant to stay" or
"deliberate". It is still debt; the goal is no admits. `--view assumed`
tags such admits "(signed off for now)"; STATUS's three mentions and
tcb-accounting.md's G4 are updated.

---

## 2026-09-23 (night) — tcb-report no longer knows about etcd-raft

At Upamanyu's direction: the tool must not be specialised to the election
proof. It had one real hardcode — `DEFAULT_PROOF_ROOT =
"new/proof/go_etcd_io/raft"`, so a bare `etc/tcb-report.py` silently
reported on etcd-raft — plus docstrings, comments and `rocqscan.py`
self-test fixtures written in this proof's names (`own_raft_ghost`,
`raft_election_safety`, `v3.v`, `election_proof/`, `Follower | Candidate |
Leader`, `raft.raft.poll`, `tracker.ProgressTracker`, …).

`--proof-root` is now **required** (except for `--selftest`); with none the
tool exits 2 with "name the development to report on". Every example is
generic (`pkg.t.run`, `Lib.proof.pkg.m`, `foo/` beside `foo.v`), with the
fixtures keeping the same syntactic shapes. What the tool still knows is
conventions, not a development: Perennial's `{{{ }}}` triples, Goose's call
forms, the collection layout, the `(* Trusted *)` marker, and this
repository's `new/should_build.v` build root.

Verified: all three self-tests pass, and 12 captured outputs —
`check-module-discipline.py` three ways (which shares `rocqscan.py`),
`tcb-report.py` in every view, scoped and not, and JSON — are
**byte-identical** before and after, with `--proof-root
new/proof/go_etcd_io/raft` passed explicitly. Every runnable invocation in
CONTRIBUTING.md, AGENTS.md, STATUS.md and tcb-accounting.md now passes it.

Not changed, deliberately out of scope: `check-module-discipline.py` has the
same `DEFAULT_PROOF_ROOT` hardcode (line 75).

---

## 2026-09-23 (late) — merged to main without a finished build

After merging `main` into this branch (`157cb9b14`: the ghost-state
construction onto the `election_proof/` layout), the build of the merged tree
was **stopped at Upamanyu's request** — the machine was needed for other
work — and he is building elsewhere. Where it got to: `.vos` closure clean
(331 files, including the new `protocol.v` and its `From Perennial Require
Import NamedProps`); `.vok` 206 of 336 raft files, 0 errors. The rest,
including most of the `Step` helpers, is unchecked on this tree. STATUS
says so under "Build state of this tree".

Then pushed to `main` as a fast-forward, and the branches this work used
deleted: `worktree-tcb-report-audit` (the pre-rebase copy) and
`worktree-tcb-report-audit-rebased` (now contained in `main`).

**If CI goes red after this push**, the likely places, in order: a file
downstream of `main`'s `spec_raft__Step.v`/`protocol.v` change that nobody
re-checked; universe constraints, which `-vok` never checks; and
`v3_proof/readonly.v`, which `make ci` compiles to `.vo` for the first time
now that `should_build.v` requires it.

---

## 2026-09-23 (night) — `main` merged into `raft-phys-one-predicate`, checked

`6071e5f91` merges `origin/main` (the constructed election ghost state, on
the `election_proof/` layout) into the one-predicate refactor. Conflicts
were in the notes (`decisions.md`, `journal.md`, `STATUS.md`: both sides
kept, `main`'s first in `decisions.md`) and in `election.v`, where the
`nstate` → `pstate` rename of this branch was ported onto `main`'s new
`election_proof/election.v`.

Checked: `.vok` of all 333 targets under `election_proof/` plus
`v3_proof/readonly.v`, 0 errors. `STATUS.md`'s counts were re-run on the
merged tree: 209 lemmas on the election path; 66 definitions, 701 lines;
TCB 5.2%.

Follow-up work (one predicate per *object* -- the tracker, `Progress`,
`Inflights`, the log, `readOnly`) continues on `raft-object-predicates`,
branched from this merge.

---

## 2026-09-23 (night, later) — one predicate per object below the raft struct

On `raft-object-predicates`, branched from `raft-phys-one-predicate`.
Asked "are there other predicates that own the same physical state as
`own_raft_phys`, or several shapes of one object?" (election path only;
the readOnly proof is out of scope) -- five, all fixed:

- **Tracker.** `own_raft_phys` held a persistent copy of the progress map's
  points-to beside the one in `own_tracker`. `own_tracker` is now indexed
  by the map (`own_tracker cfg tv votes prs`); the copy is gone. The `Visit`
  closure returns the tracker at the same `prs`. `stepLeader`'s
  `MsgVoteResp` spec read the copy, so it now takes `s.lent = None` (its
  caller has `nstate_wf`).
- **`Progress`/`Inflights`.** `own_progress pr pv iv`, `own_inflights l iv
  buf` only; `grow`, `reset`, `ResetState` restated on them.
- **`readOnly`.** `newReadOnly` returns `own_read_only ro` only.
- **Log.** `own_raftLog l (ls : logstate.t)` -- entry list, `committed`,
  `applied`, page on loan -- is the one predicate; `_at` names dropped.
  `own_unstable` for the embedded struct. `own_raft_phys` quantifies `ls`
  (not in `nstate.t`: decisions.md).

Two commits (`f1ecc4cf3` tracker/Progress/Inflights/readOnly; the log one
after it), each checked with a full `.vok` sweep: 333 targets, 0 errors.
Then `raft-phys-one-predicate` merged in for its notes. `tcb-report
--scope election_proof`: 211 Qed lemmas, 67 definitions / 719 lines, TCB
5.3%, axioms unchanged (10 + the trusted `wp_raftLog__slice`).
`check-module-discipline --scope election_proof`: the same 5 notes/warnings.

What bit (gotchas.md, "Working at a record-indexed predicate"): `iNamed`
does not unfold a plain `∗`-chain definition; a `⊣⊢` unfold lemma used with
`iDestruct` just unfolded the definition; spec postconditions at
`logstate.mk …` need `logstate_simpl` before `lia`; and `eq_refl` for a
state premise needs the state spelled out.

`newRaft` (the original task) is still deferred; `committed`/`applied` now
survive `lastEntryID`, which was one of its blockers.

(2026-09-24) `raft-object-predicates` was fast-forwarded into
`raft-phys-one-predicate` and deleted, locally and on `origin`; work
continues on `raft-phys-one-predicate`.

---

## 2026-09-24 — `own_raft_phys` sealed; program proofs use field lemmas

Branch `raft-phys-field-lemmas` (from `main` at `3bcd64960`). Asked to make
`own_raft_phys` an abstraction program proofs never unfold, with a lemma per
field access and, for maps, an accessor that lends the inner object out
rather than a lemma per map operation. Done; the design and what was
rejected are in decisions.md ("Program proofs do not unfold
`own_raft_phys`"), the traps in gotchas.md ("Working against the sealed
`own_raft_phys`").

- `inv_raft_phys.v`: `own_raft_phys` is sealed, and its last section is the
  interface -- `wp_raft_load_<f>`/`wp_raft_store_<f>` for the fields the
  election path touches, the accessors (`own_raft_phys_tracker`(`_same`),
  `_log`, `_msgs`, `_msgsAA`, `_readOnly`), the loan lemmas (`_lend`,
  `_unlend`, `_trk_lent`), `own_raft_phys_eq`, and `wp_raft_log`. `wp_log`
  is gone. `inv_misc.v`: `own_raft_misc_option`/`_swap` replaced by
  `own_read_only_option`.
- All 28 program proofs that opened the predicate were rewritten against it
  (six by hand as a pilot, the rest by five parallel agents with a shared
  brief). None has an `iNamed "Hphys"`, a re-seal, or an `_unless_` lemma
  left, and the seal makes sure of it.
- A first version had a `wp_raft_field` tactic that tried every field lemma
  in turn. Asked to make sure that was not slowing proofs down, it was
  removed: instrumented to print the lemma each of its 110 call sites used,
  every proof run once, and each site rewritten to the explicit
  `wp_apply (wp_raft_load_<f> with "Hphys") as "Hphys"` sequence (8 by
  hand: `repeat` and multi-goal sites). Cold `rocq-warm` time over the 28
  proofs, two at a time on a shared box: **1919s with the search, 1545s
  explicit** (about 20%; `becomeFollower`, `becomeCandidate`, `becomeLeader`,
  `hup` and `reset` 35-45%).
- `inv_raft_phys.v` itself went from ~70s to ~200s cold with ~45 new lemmas.
  Unsealing the 33-field struct and re-framing it field by field had made it
  ~330s; the positional split (`split_field_proof`) brought it down.

Checked: `.vok` of all 333 targets under `election_proof/` plus
`v3_proof/readonly.v`, 0 errors. `tcb-report --scope election_proof`: 255
Qed lemmas, 69 definitions / 721 lines, TCB 5.3%, assumptions unchanged (10
`Axiom` + the trusted `wp_raftLog__slice`). `check-module-discipline`: the
same 5 notes/warnings.

Not done: `own_raft_phys_intro` is still public -- it is the constructor a
`newRaft` spec will need, and nothing but that should use it.

## 2026-09-24 — `newRaft` proved: `own_raft_phys` has a constructor

Branch `newraft`, off `raft-phys-one-predicate` (`3bcd64960`). Goal: prove
`newRaft`, or exhibit bugs in the existing definitions that make it
impossible. It is proved (`NewRaft.wp_newRaft`, `spec_newRaft.v`), modulo
four new `Axiom`s for untranslated code, and it turned up four definitional
problems -- none of which blocked the proof, all recorded in STATUS item 1.

### What was built

Twenty new collections: `newRaft` and its callees `Config.validate`
(+ `IsLocalMsgTarget`), `newLogWithSize`, `tracker.MakeProgressTracker`,
`traceInitState`, `traceConfChangeEvent`, `raft.switchToConfig` (non-leader
case only), `ProgressTracker.ConfState` (+ `MajorityConfig.Slice`),
`assertConfStatesEquivalent`, `IsEmptyHardState` (+ `isHardStateEqual`),
`raft.loadState`, `raftLog.appliedTo`, `ProgressTracker.VoterNodes`; and
the axioms `confchange.Restore`, `raftpb.ConfState.Equivalent`,
`fmt.Sprintf`, `strings.Join`. `newRaft_post_init` (`election.v`): an empty
`HardState` gives `nstate_rel s init_pstate`. `v3_proof/base.v`'s
`is_initialized` gains `emptyState ↦□ HardState{}` (read by
`IsEmptyHardState`), so everything downstream was re-checked.

**How `newRaft` fits the one-predicate rule.** The struct satisfies
`own_raft_phys` with the tracker and log **on loan** (`nstate.lent = Some
tv0`) from the moment it is allocated -- `own_tracker` cannot hold of the
empty tracker `MakeProgressTracker` builds (`Hcfg_ne`). `switchToConfig`
takes the loaned struct plus `own_tracker` of the new tracker value;
`loadState` and `appliedTo` work on the loaned `own_raftLog`; the loan ends
just before `becomeFollower`, which needs `lent = None`. No variant
predicate and no `ls` in `nstate.t` were needed (STATUS item 2).

### Found

1. **`own_tracker`'s `HmaxInfl` comment was false**: it said `validate`
   bounds `MaxInflightMsgs` to `(0, 1<<30]`; `validate` checks only `> 0`.
   So `own_raft_phys` excludes valid configs with `MaxInflightMsgs ≥ 2^62`;
   `newRaft` takes the bound as a premise. Comment fixed,
   false-statements.md row added.
2. **`own_raftLog` forgets its storage.** `logstate.t` has no storage
   field, so a caller holding the same `Storage` interface value by another
   route (`newRaft`: `c.Storage.InitialState()` after `newLogWithSize`)
   cannot use the log's `own_Storage`. `newLogWithSize`'s postcondition is
   therefore stated unfolded, with `lv.storage = st`. Fix: add the field.
3. **An empty `ConfState` is outside `own_raft_phys`** (`Hcfg_ne`) -- the
   state of a node joining an existing cluster. Scope, not a bug; now in
   the scope table.
4. **Two of the four new axioms are core raft** (`Restore`, `Equivalent`).
   `Restore`'s premise `voters ≠ []` is needed for the axiom's *soundness*:
   with no voters `chain` runs no ops and returns the input maps themselves,
   which the premise already owns.

What remains for satisfiability: an `is_Storage` instance (`MemoryStorage`).

### Proof-engineering notes

In gotchas.md ("Proving a long function with sequential `if`s"). The one
that cost most: splitting each `if` and carrying on under `all:` gave eight
copies of the goal and rocq-warm's 4.2 GB ceiling; joining the arms with
`wp_bind (if: _ then _ else _)%E` + `wp_wand` fixed it.

### Evidence

- `proof_newRaft.v`: `-vok` **353 s**, exit 0; every new `proof_*`/`link_*`
  and `spec_newRaft`/`spec_newLogWithSize` checked with `make … .vok`.
- `etc/check-module-discipline.py --scope election_proof`: the same 6
  notes/warnings as before, no errors.
- `etc/tcb-report.py --proof-root new/proof/go_etcd_io/raft --scope
  election_proof`: 14 `Axiom` (was 10) + 1 `Admitted`; two results
  (`Step`, `newRaft`); 228 `Qed` lemmas; 74 definitions / 812 lines; TCB 5.5%.
- Full `.vok` sweep after the `base.v` change: `make -k -j2` of every `.v`
  under `new/proof/go_etcd_io/raft/` plus `etcd/server/v3/etcdserver.v` (which
  imports it): **exit 0, 417 files checked, no errors**.

## 2026-09-28 — `main` (the sealed `own_raft_phys`) merged into `newraft`

`main` gained `own_raft_phys` sealed behind field lemmas and accessors
(entry "own_raft_phys sealed" above). Merged into `newraft`; only the notes
conflicted. Three of this branch's proofs unfolded the predicate and were
ported to the interface: `switchToConfig` (now stated at the setter form
`s <| lent := Some tv |>` that `own_raft_phys_trk_lent` works at; uses a new
`wp_raft_store_isLearner`, a store of the pinned value `false`), `loadState`,
and `newRaft` (still constructs the struct with `own_raft_phys_intro`, the
one legitimate use; ends the loan with `own_raft_phys_unlend`, reaches the
tracker with `own_raft_phys_tracker_same` and the log with
`own_raft_phys_log`). Two traps from `switchToConfig`: `(!ok || r.isLearner)`
short-circuits, so on the `ok = false` path `isLearner` is never loaded and
`r.state` is loaded twice; `wp_apply` of a load lemma that is not in
evaluation position fails with "cannot apply", not "not found".

The unfinished refactor (log state into `nstate.t`) is stashed as
`newraft-phaseA-logst-wip-a548c275`; it was written against the unsealed
predicate and is being redone against the accessors.

Checked: `.vok` of all 417 targets (every `.v` under `raft/`, plus
`etcd/server/v3/etcdserver.v`), 0 errors. `tcb-report --scope
election_proof`: 273 Qed lemmas, 14 Axiom + 1 Admitted, two results, 76
definitions / 817 lines, TCB 5.5%. `check-module-discipline`: 6
notes/warnings, no errors.

## 2026-09-29 — The log's state in `nstate.t`; the log is never on loan

Asked to move the log's state into `nstate.t` and work towards removing
`nstate.lent`. First step done (on `newraft`, after merging the sealed
`own_raft_phys` from `main`).

- `defs.v`: `logstate.t` moved here from `inv_raftlog.v`; `nstate.t` gains
  `logst`. New `log_last`, `log_append`, `stamp` (moved from
  `proof_raft__appendEntry.v`), `leader_entry`, `become_leader_pre`;
  `become_leader` now *includes* the append of the stamped empty entry.
  `nstate_idle s := lent = None ∧ logst.page = None` is the premise every
  function touching the tracker or the log takes (it replaced the bare
  `lent = None` in 17 specs and local lemmas); `nstate_wf` uses it.
- `inv_raft_phys.v`: `own_raft_phys` owns `own_raftLog rv.raftLog s.logst`
  unconditionally; `own_raftLog_unless` is gone. Accessors:
  `own_raft_phys_log_at` (take out, put back at any `ls'`, state
  `s <| logst := ls' |>`), `own_raft_phys_log_same` (put back at the same
  state; no premise), `own_raft_phys_log` (old shape, kept for its callers).
  `_lend`/`_unlend` move the tracker only.
- Specs that now say more: `appendEntry` returns the log at
  `log_append s.logst (imap (stamp s.term (log_last s.logst)) ents)` (it used
  to return the struct at the *same* `s`, true only because the log was
  quantified away), `becomeLeader` at the new `become_leader`, `loadState`
  at `logst.committed := hs.Commit`.
- The pattern every log-reading proof now follows: the log cannot be held
  outside the struct across a field load or a callee (those need
  `own_raft_phys`), so it is taken out and put back around each `raftLog`
  access. Ported by hand: `appendEntry`, `becomeLeader`, `loadState`,
  `newRaft`; by subagents (one file each, shared brief):
  `maybeSendAppend` (the page loan is now in `logst.page` across `send`;
  its `msa_pkg` carries the struct), `reset` (the `Visit` closure rebuilds
  the struct around its `lastIndex()` calls), `hasUnappliedConfChanges` (no
  tracker loan at all any more), `maybeSendSnapshot`.

Checked: `.vok` of all 412 targets under `election_proof/`, 0 errors.
`tcb-report --scope election_proof`: 274 Qed lemmas, assumptions unchanged
(14 Axiom + 1 Admitted), 76 definitions / 816 lines. `check-module-discipline`:
same 6 notes/warnings.

Next: `own_tracker` at the empty configuration (so `newRaft` needs no
loan), then pin a `Progress` value in `nstate.t` instead of lending the
tracker, then delete `lent`.

## 2026-09-29 (later) — `own_tracker` at the empty configuration; `newRaft` lends nothing

Second step towards removing `nstate.lent`.

- `inv_tracker.v`: `own_tracker` no longer requires `cfg ≠ ∅`. It gains
  `AutoLeave = false` (a simple configuration; needed because
  `switchToConfig` no longer holds the tracker value across the call, so
  `ConfState` has to say `AutoLeave = false` itself). New: `own_config` (the
  pieces `confchange.Restore` builds), `own_tracker_empty` (what
  `MakeProgressTracker` returns is `own_tracker ∅ …`), `own_tracker_reconfig`.
- `cfg ≠ ∅` is now a premise of `JointConfig.VoteResult`, `TallyVotes` and
  `poll`; `stepCandidate` derives it from `id ∈ cfg` (subagent).
  `ConfState` rules out the nil voter map with `own_map_not_nil` instead.
- `inv_raft_phys.v`: `own_raft_phys_reconfig cfg0 cfg`, the one accessor
  that changes the `cfg` index. `switchToConfig` is stated on it:
  `own_raft_phys cfg0 r id s ∗ own_config cfg … → own_raft_phys cfg r id
  (s <| progress := prs |>)`, no loan. `confchange.Restore` takes the old
  progress map at `↦$□`.
- `newRaft` builds its struct over `∅`, idle, and never lends anything.

Checked: `.vok` of all 412 targets under `election_proof/`, 0 errors.
`tcb-report`: 277 Qed lemmas, assumptions unchanged.
`check-module-discipline`: 6 notes/warnings.

Next: pin a `Progress` value in `nstate.t` for `maybeSendAppend`,
`maybeSendSnapshot`, `reset`; delete `lent`.

## 2026-09-29 (later still) — the log holds its entries read-only; `logstate.page` is gone

Asked to remove `logst.page`, `nstate.lent` and `nstate.pin` (the last
never committed: `nstate.t` is to hold only physical fields, and a pin is
not). This entry is the first of the three; decision in decisions.md,
"The log holds its entries read-only".

- `slice_persistent.v` (new): `wp_slice_append_persistent`, Go's `append`
  onto a destination held `↦*□` with its slack owned. `wp__new_cap`
  needed `(V:=V)` (statement bug in `slice.v`; todo.md).
- `inv_storage.v`: `Entries` returns `s ↦*□ es`, no wand (the `Storage`
  interface's own contract, `storage.go:56-67`).
- `inv_raftlog.v`: `own_unstable u uv uents` (no `page` argument) and
  `own_raftLog_core` hold the unstable entries `↦*□`; `own_raftLog` has
  no match on a page; `own_raftLog_lend_page`/`_return_page`,
  `own_unstable_return_page` deleted. The persistent conjuncts are named
  *spatially* (`"Huents"`, not `"#Huents"`): with `#`, re-opening the
  predicate clashed on the name and `iFrame "∗"` stopped framing them.
- `defs.v`: `logstate.page` deleted; `nstate_idle s` is `lent = None ∧
  True` until `lent` goes.
- Specs: `unstable.slice`, `raftLog.slice`/`entries` return `↦*□` and the
  log unchanged; every `page = None` premise (14 specs) deleted.
  `own_raft_phys_log` (the old-shaped accessor) deleted; callers use
  `own_raft_phys_log_same`.
- `raftLog.slice`'s proof re-seals the log at each exit (`reseal_log`);
  its `extend` exits persist the fresh slice under `wp_fupd`. 605s → 709s.
- The word "page" (invented, not etcd's) is gone from the proofs and
  notes except for `raftLog.scan`'s own `pageSize` batches (subagent).
- New: notes/todo.md, a log of deferred work (wp__new_cap, moving the
  append lemma into `slice.v`, `nextUnstableEnts`' uncapped slice).

Checked: `.vok` of all 412 targets under `election_proof/` (sweep, 0
errors). `tcb-report --proof-root …/election_proof`: 14 Axiom, 1 Admitted
(unchanged), 272 Qed, 76 definitions / 807 lines. `check-module-discipline`:
6 notes/warnings (unchanged).

Next: `lent`. `reset` and `maybeSendSnapshot` can drop the loan without
new state (Visit's invariant = the tracker accessor's wand, as in
`bcastAppend`); `maybeSendAppend` needs each peer's `Progress`/`Inflights`
values in `nstate.t` (STATUS item 2).

## 2026-09-29 (last) — `nstate.lent` is gone: each peer's `Progress` value is in `nstate.t`

Second and third of the three removals (`logst.page` was the first,
above; `nstate.pin` was never committed). Decision in decisions.md, "Each
peer's `Progress` value is in `nstate.t`".

- `defs.v`: `nstate.prvals` replaces `lent` (same position); `nstate_idle`
  deleted; `nstate_wf` is the `r.step` equation alone.
- `inv_tracker.v`: `own_tracker … prs pvs` (`big_sepM2`);
  `own_tracker_lookup` returns the value and takes it back at any new one;
  `own_tracker_lookup_same`, `own_tracker_prvals_dom`,
  `big_sepM_exist_sepM2` (for `own_tracker_reconfig`, whose `Restore`
  output has existential values); `visit_closure` hands the closure the
  value and quantifies the returned ones.
- `inv_raft_phys.v`: the tracker is always owned; lend/unlend/trk_lent
  deleted; new `own_raft_phys_tracker_prvals` (take the tracker back at
  new values) and `own_raft_phys_pr` / `_upd` / `_any` (one `Progress` by
  its key, premises as pure wands -- gotchas.md).
- Specs: 16 `nstate_idle` premises gone; the 11 functions that write a
  `Progress` quantify the new values in the postcondition.
- Proofs without a loan: `reset` (`Visit` invariant = accessor wand),
  `maybeSendSnapshot`, `maybeSendAppend` (borrow `pr` around each
  stretch; `send` keeps `prvals`), `bcastAppend` (lead). The other 23
  proof files threaded the new binder (subagent, from a written brief).
- Notes: raft-implementation-facts.md records which slices raft hands out
  uncapped (answering an open question): only `readOnly.maybeAdvance`'s
  result can overwrite live data, and its one caller never appends.

Checked: `.vok` of all 412 targets under `election_proof/` (sweep, 0
errors). `tcb-report --proof-root …/election_proof`: 14 Axiom, 1 Admitted
(unchanged), 274 Qed, 74 definitions / 802 lines. `check-module-discipline`:
6 notes/warnings (unchanged).

## 2026-09-29 — the two framework todo.md items: `wp__new_cap`, `wp_slice_append_persistent`

- `new/golang/theory/slice.v`: `wp__new_cap` moved above the `wps`
  section's `Context [V] …`, so it no longer quantifies over an unused type
  and its two instances (which `wp_apply` left as shelved goals outside the
  section). `wp_slice_append_persistent` moved in from
  `election_proof/slice_persistent.v`, right after `wp_slice_append`, now
  using a plain `wp_apply wp__new_cap`.
- `election_proof/slice_persistent.v` deleted; `inv_raftlog.v` no longer
  requires it (it gets `slice.v` through `inv_storage.v`).
- Notes: both todo.md "Framework" entries deleted, the gotchas.md
  `(V:=V)` entry deleted, decisions.md points at the new location.

Checked: `slice.vo` (full), `new/should_build.vos` (whole closure), `.vok`
of `inv_raftlog.v` and `proof_unstable__truncateAndAppend.v`. `tcb-report
--proof-root …/election_proof`: 14 Axiom, 1 Admitted (unchanged), 273 Qed
(274 before: `wp_slice_append_persistent` left the proof root for
`slice.v`). Found on the way, not caused by this change: the full `vo` build
fails in `chan/au_spec/chan_au_recv.v:360` (reproduced on 2e7f3e69b) and
`chan_au_send.v:655`; STATUS item 11. `rocq` needs
`$HOME/.opam/perennial/bin` on `PATH` (gotchas.md).

## 2026-09-29 — `chan/au_spec` builds again: `done` on a dead `WP` branch

What broke: the full `vo` build failed with "No applicable tactic" in
`chan_au_recv.v` and `chan_au_send.v` (STATUS item 11, now deleted). Four
sites, not two -- each `-vok` stopped at the first:
`chan_au_recv.v:360` (`done`, context has `Hl : length (v :: buffer) = 0`),
`chan_au_recv.v:782` (`wp_Receive`), `chan_au_send.v:655` (`wp_Send`) and
`chan_au_send.v:865` (`wp_Close`), the last three `wp_if_destruct; first
done.` with `Hnn : null ≠ null` in the context.

Root cause: 25ce5ca6f (2026-09-17, "make wp tactics linear-cost-free")
added `Ltac done ::=` in `new/golang/theory/proofmode.v`. On an
`envs_entails _ (wp …)` goal it runs only `fast_done`/`trivial` with the
program let-bound; stdpp's `discriminate` / `contradiction` / `¬_`-case arms,
which used to close these dead branches, are no longer tried. Found by
printing the goal at `chan_au_recv.v:782`; not bisected. The raft
`.vos`/`.vok` sweeps never ran these proof bodies, so nobody noticed.

Fix: `by exfalso` at all four sites (`{ done. }` -> `{ by exfalso. }`,
`first done.` -> `first by exfalso.`). With the goal `False` the non-`WP`
arm of `done` (stdpp's cascade) closes it. The override itself is left as
is; gotchas.md has the trap.

Checked: `make …/chan_au_recv.vok` 0, `make …/chan_au_send.vok` 0;
`make -j4 …/chan_au_recv.vo …/chan_au_send.vo` 0 (rebuilt stale deps);
downstream `make -k -j4 new/golang/theory/chan.vo` plus all eleven
`chan/idioms/*.vo` 0. Not run: `make ci`.

## 2026-09-29 — `wp_slice_append_dfrac`: one `append` spec for any fraction on the destination

The todo.md framework item, as the user specified: a general
`wp_slice_append_dfrac` (destination `s ↦*{dq_s} vs` with a pure premise
`⌜✓dq_s⌝`, result `s' ↦*{dq_s} (vs ++ vs')`), with `wp_slice_append`
(`DfracOwn 1`) and `wp_slice_append_persistent` (`DfracDiscarded`) as
two-line wrappers keeping their old statements, so no caller changed. The
proof is the old persistent one with `own_slice_update_to_dfrac` in place
of `own_slice_persist`. `✓dq_s` cannot be dropped: `s ↦*{dq} []` holds no
resource (gotchas.md), so with `dq = DfracOwn 2`, `vs = []` and a
non-empty `vs'` the postcondition would be `False`.

Checked: `slice.vo` (full). `make -k -j4 ci`: all eight callers outside
the failing cones built as `.vo` (bytes, std, strings, unittest,
elimination_stack, channel_google, channel_fibonacci, chan_au_send); five
pre-existing `done`-override failures (STATUS item 11) blocked the rest, so
the other eight callers were checked by `.vok` after rebuilding
`new/should_build.vos`: truncateAndAppend, raft__send,
MajorityConfig__Slice, ProgressTracker__VoterNodes, newRaft,
raft__campaign, v3_proof/readonly, tchajed/marshal — all exit 0.
