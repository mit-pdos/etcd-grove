# k8s 7f-5 handoff (2026-11-13; branch `k8s-7f5`, worktree `/shared/etcd-grove-k8s7f`)

**Read first:** `notes/k8s-7f5-scope.md` (this stage's Scope, for etcd-grove-81's review),
`notes/k8s-7f-scope.md` (the parent plan; §2, §4, §5.3), `notes/k8s-7f4-freeze.md` (the context-key
refutations T-h..T-k: the lesson for every trusted context text), `/shared/tmp/coord-81/common-rules.md`,
the worktree's untracked `questions.md` (decisions; never re-add it tracked).

## Done
- Branch `k8s-7f5` off lean `222c3fcff7` (k8s-7f4 merged and deleted).
- The Scope (`notes/k8s-7f5-scope.md`), reviewed: 81 decided Q1-Q7 as recommended (§8 there, questions.md).
- S0 (enumeration, Go evidence `examples/premisefix/watcherctx`, Goose dry run, the driver's
  `watchList()`, the no-other-mutator check) and S1 (T5-b in `CtxKeys.lean`, T5-c in `Gate.lean` with
  `watchList`'s spec/proof and the `Main*` proofs; T5-d text only): `notes/k8s-7f5-freeze.md`.

## State
- Dependencies (Scope §2): 7f-3 **missing** (not started); 7c-3 and 7e-1 **landed** (7c-3 folded into
  7e-1, 7e Freeze `8809f94d74`); sweep repairs B5 **landed with `featureOff` only** (`featureOn` is
  this stage's T5-c); 7f-0 partial (records only; the rest goes with 7f-6, Q7).
- No Lean edited. Nothing built on this branch.

## Next, in order
1. DONE (`23af282dca`): S1 built (full build passes), checks in `notes/k8s-7f5-freeze.md` "Checks"
   (tcb: NEW `k8sfeature.featureOn_persistent`, also in collection k8setcd3; not updated). STOPPED for
   81's axiom review of S1.
2. After the review: apply its fixes; `etc/tcb-report.py --check --update` and the k8setcd3
   collection's `--update`; STATUS entry; merge lean; land S1 via etc/land.sh (81's go). Then 7f-3a statements (with T5-a's translation: the dry-run
   patch `/shared/tmp/k8s7f5/goose-dry-full.patch` has the client/metadata toml lines), STOP (S2).
3. 7f-3b/3c, and 7f-5a's Draft in parallel (Q1), STOP (S3) at the Draft.
4. Left from S0: the many-watches check (Scope §5: `isClientWatcher` persistent, repeated `Watch`).

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
