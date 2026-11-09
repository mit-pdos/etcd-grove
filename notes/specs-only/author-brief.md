# Brief: the author of a batch

You write the specs of one batch (`batches.md`) on the specs-only branch, in the worktree
`/home/ubuntu/etcd-grove/.claude/worktrees/specs-only` (shared with other batches' agents: touch
only your own paths, below). No proofs: specs, vocabulary, laws, Go requirement snippets, and the
block comments that argue for them.

## Read first

1. `notes/specs-only/README.md` (what a spec is here: files, Lean conventions, snippets, reviews).
   `Spec/smoke/Api.lean` is a compiled example of the Lean forms.
2. Your batch's row in `notes/specs-only/batches.md`, and `notes/specs-only/req/<pkg>.md` for each of
   your packages, if it exists: what your callers' batches need from you.
3. The spec skill: `.claude/skills/spec/PRINCIPLES.md` in full, and the examples
   (`.claude/skills/spec/examples/README.md` indexes them) whose subject is your package or whose
   principles you rely on.
4. The vocabulary already on the branch that you build on (the anchor's `Spec/go_etcd_io/etcd/api/v3/
   Model.lean` and `Spec/go_etcd_io/etcd/client/v3/Api.lean`, once written; other batches' `Api.lean`
   files as they appear).
5. The Go code of your batch (pinned: `.lake/src/...`), and the old specs of your functions
   (`/home/ubuntu/etcd-grove/.claude/worktrees/specs-ref/Spec/<pkg>/`) with what their proofs needed
   (`specs-ref/Proof/<pkg>/`), and the old notes on your package (`specs-ref/notes/`: grep its
   name in `decisions.md`, `STATUS.md`, the plans; `specs-ref/issues/`, `nonissues/` for known bugs
   and preconditions). The old specs are a starting point, not a constraint: many assumed what the
   proofs of the time could not avoid (a put without a lease, auth off, no compaction, a first start
   only, one member). Relax every such assumption the code does not need.

## Do

1. **Users.** Find every user of your batch's API (the callers outside your batch: in the pinned
   etcd and raft sources, `examples/`, the Kubernetes code). Group the uses into patterns.
2. **Snippets.** For each pattern, a minimal Go snippet in `examples/specreq/<alias>/` (README,
   "Requirement snippets"): what the callers rely on as a `panic` on its violation, assumptions in
   the header. Check them: `cd examples && go vet ./specreq/<alias>/` (or `gofmt -l` for an
   `//go:build ignore` file).
3. **Vocabulary.** `Spec/<pkg>/Api.lean` (and `Model.lean` if large): opaque ghost-name types, pure
   models, opaque predicates, laws as `.spec` obligations; its header says what each predicate means
   and how its owner would realize it (the invariant, the ghost state, the callee predicates). Fewest
   abstractions that serve every user (PRINCIPLES, "Abstractions").
4. **Specs.** One `Spec/<pkg>/<fn>.lean` per function, with its block comment (Users, Proof sketch,
   Changes, Margin). The core API with full care; an internal helper's spec may mirror its code and
   its comment may be two lines. A function whose spec your sketches never use and that nothing
   calls may be left out: list it in your report.
5. **Callees.** What your proof sketches need from another batch's API goes in
   `notes/specs-only/req/<callee pkg path, / as _>.md`, appended under a heading `## from <your
   batch id>`: the need in plain terms, the Go snippet of your use, which of your sketches relies on
   it. Do not edit other batches' files. If a callee's `Api.lean` already exists, cite its predicates
   and specs in your sketches by name; else describe what you assume of them.
6. **Build.** `etc/specs-build.sh --dir Spec/<pkg>` for each of your directories (never `lake build`
   directly). Every file must build. Fix what does not.
7. **Report.** `notes/specs-only/batch-<id>.md`: the files, the exported vocabulary (each predicate
   and law, one line), the main changes from the old specs (relaxed premises, restated
   abstractions), the functions left out, the open questions for the user (a decision that is
   theirs: a new premise on a client-facing spec, a scope restriction), the `req/` sections you wrote.
   Your final message: the same, short.

## Don't

- No `theorem`, `axiom`, `sorry`, `instance`, `example` or proof. No edits outside `Spec/<your
  packages>/`, `examples/specreq/<your aliases>/`, `notes/specs-only/batch-<id>.md`, and appends to
  `notes/specs-only/req/*.md`. No git commands that change anything (no commit, stash, checkout,
  reset): the coordinator commits.
- No vocabulary from the old `Proof/` tree (it is gone): restate what you need, opaquely.
- No spec family for a special case, no premise only the old proof needed, no implementation detail
  in a client-facing statement.

## Repairs

The coordinator will send you the reviewers' reports. Fix every first-tier finding (a hard-rule
violation: unsound, incomplete for a user, a snippet not provable), or answer it in the report if
you think it wrong (with the code or spec that shows it). Rebuild, and update your report.
