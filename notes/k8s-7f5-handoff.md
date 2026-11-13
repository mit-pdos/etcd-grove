# k8s 7f-5 handoff (2026-11-13; branch `k8s-7f5`, worktree `/shared/etcd-grove-k8s7f`)

**Read first:** `notes/k8s-7f5-scope.md` (this stage's Scope, for etcd-grove-81's review),
`notes/k8s-7f-scope.md` (the parent plan; §2, §4, §5.3), `notes/k8s-7f4-freeze.md` (the context-key
refutations T-h..T-k: the lesson for every trusted context text), `/shared/tmp/coord-81/common-rules.md`,
the worktree's untracked `questions.md` (decisions; never re-add it tracked).

## Done
- Branch `k8s-7f5` off lean `222c3fcff7` (k8s-7f4 merged and deleted).
- The Scope drafted (notes only): `notes/k8s-7f5-scope.md`. STOPPED for 81's review (Q1-Q7 there).

## State
- Dependencies (Scope §2): 7f-3 **missing** (not started); 7c-3 and 7e-1 **landed** (7c-3 folded into
  7e-1, 7e Freeze `8809f94d74`); sweep repairs B5 **landed with `featureOff` only** (`featureOn` is
  this stage's T5-c); 7f-0 partial (records only; the rest goes with 7f-6, Q7).
- No Lean edited. Nothing built on this branch.

## Next, in order (after 81's answers)
1. S0: the context and error-method enumeration (Scope §4.1), the Goose dry run of the configuration
   (with a targeted build), `examples/premisefix/watcherctx` tests, the many-watches check (§5).
   Then STOP (S1) with the trusted package for the axiom review.
2. 7f-3a statements, STOP (S2). Then 7f-3b/3c, and 7f-5a's Draft in parallel (Q1), STOP (S3) at the Draft.

## Pitfalls
- Every trusted text over a context must state every `ctx.Value` key the modelled code reads,
  and the methods called on what it returns (APF's `Signal()`: `apf_context.go:50-51`).
- `prevKv` none is reachable without compaction (`issues/etcd-watch-prevkv-before-created.md`): the
  client spec must admit it.
- `watchGRPCStream.run` (3368 lines): check with `etc/lean-check.py --fast --split`.
- The etcd fork's sources at the pin `0b50f0426` are in the module cache
  (`~/go/pkg/mod/github.com/upamanyus/etcd/{client,server,api}/v3@v3.0.0-20261112123031-0b50f04262d9`);
  `.lake/go-src/etcd` is at another revision.

## Build
Every lake command with `--packages=/shared/tmp/manifest-ddc.json` (scripts: `LAKE_OPTS=...`), under
`systemd-run --scope -q -p MemoryMax=64G`; full builds also under `flock /shared/tmp/etcd-grove-build.lock`.
Go tests under `systemd-run --scope -q -p MemoryMax=32G`, `GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`.
This worktree's `.lake/build` state: as 7f-4 left it; check `df -h /shared` before any seeding (ask 81).
