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

## Handoff point (2026-11-13, third 7f-5 agent): 7f-3a at S2 (STOPPED for 81's review)

Done (on `k8s-7f5`, not landed):
- Translation config (Q2) applied: client `WithPrevKV`/`WithRequireLeader`; grpc metadata's
  `NewOutgoingContext`, `Pairs`, `MD.Copy`, `MD.Set`, `copyOf` (imports context/strings/fmt);
  `etc/goose.py --project etcd`, `--check` passes; `etc/gen-init.py` (metadata Init + 17 PkgTables);
  SpecPlan PkgInit for metadata only (the generator's other drift is lean's, ungated, left alone).
  The axiom `WithRequireLeader.wp_proof` still stands over the translated function.
- `EvModel` gains `prevKv : Loc := null` (InvStore.lean; InvWatcher's countable instance updated).
- The statements: `Proof/go_etcd_io/etcd/client/v3/Draft7f3a.lean` (unlinked; `P`-suffixed new
  forms + `WithRequireLeader.specGen`; laws proved, no sorry/axiom), the Draft
  `notes/k8s-7f3a-draft.md` (table old → new, findings, plan, decisions D1-D3).
- Findings: (1) Q2's "no new axiom" is false: translating WithRequireLeader needs WithValue.spec
  at grpc's key (+ valueCtx fields, watchCtx), an intro law for opaque builtRawMD (ToLower too weak
  for its case clause), FromOutgoingContext over a non-isContext parent; recommended the fallback
  (one restated axiom). (2) 7f-3b: the send loop writes `PrevKv` into mvcc's events, which mvcc's
  API gives read-only (`evIs`): an mvcc API ownership change.

Next (after 81's decisions D1-D3): the full build of this config (not yet run; targeted builds
pass), then 7f-3b (mvcc event ownership, v3rpc recvLoop/sendLoop), 7f-3c (client, swap, users).

## Handoff point (2026-11-13, second 7f-5 agent): S1 LANDED (lean `be36a0f818`); 7f-3a next

S1 with the review's fixes landed (`0d873a9ee5`, `be36a0f818`; freeze note "S1 review"; gates all
passed; trust base 869 axioms, 4 sorries). The branch `k8s-7f5` is lean now; continue on it.

**Next: 7f-3a's statements, up to hard stop S2** (Scope §6 row 7f-3a; parent `notes/k8s-7f-scope.md`
§2.3 1-2, §5.1). Nothing of 7f-3a written yet. In order:
1. Translation config (no trust; from `/shared/tmp/k8s7f5/goose-dry-full.patch`):
   - `Code/go_etcd_io/etcd/client/v3.toml`: add `WithPrevKV`, `WithRequireLeader` to `translate`;
   - `Code/google_golang_org/grpc/metadata.toml`: `translate = ["!*", "NewOutgoingContext", "Pairs",
     "MD.Copy", "MD.Set", "mdOutgoingKey", "rawMD", "copyOf"]` (**copyOf**: the S1 review),
     `imports = ["!*", "context", "strings", "fmt"]`;
   - `etc/goose.py --project etcd` (not with GOWORK=off), `--check`.
   - Consequence to handle: `WithRequireLeader` is today names-only with an axiom
     (`Proof/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`, `Background()` only). Translated, that
     axiom becomes a proof over `FromOutgoingContext` (existing spec), `Pairs`/`NewOutgoingContext`
     (translated: `context.WithValue`) and `strings.ToLower` (trusted: some string): the trust base
     loses an axiom (report it; `--check --update` after 81's review). The generalized triple over a
     `watchCtx` parent (T5-a: every other key, Done/Err/Cause the parent's; the metadata "the
     parent's plus one key") is a 7f-3a statement.
2. The statements (Lean text in a Draft note, e.g. `notes/k8s-7f3a-draft.md`, for 81's S2 review;
   no `sorry` under a linked result, so do not change linked definitions before the review):
   - `OpFull.isRangeWatch` (`Proof/go_etcd_io/etcd/cache/v3/InvEtcdTxn.lean:1231`) drops
     `o.base.prevKV = false`; `wrRO`'s `prevKV ↦□ false` (`client/v3/InvWatch.lean:846,859`) becomes
     the model's value;
   - `EvModel` (`cache/v3/InvStore.lean:185`) gains `prevKv : Loc` (null = none); `eventAt`
     (`InvStore.lean:1214`) gains the `PrevKv` field; `eventIs` (`client/v3/WatchStateDefs.lean:102`)
     gains: `prevKV = false → prevKv = null`; else null (always admitted:
     `issues/etcd-watch-prevkv-before-created.md`), or, for a non-create, `kvValAt prevKv` of the
     key's kv at `ev.rev - 1` (`σ.at (r-1)`, as `KVState.revEvents`); a create's is null;
   - `rawRespOk` (`WatchStateDefs.lean:261`) the same at the server's level (`mvcc.stateAt L (r-1)`);
   - the server: `swsMu` allows `prevKV` entries (`v3rpc/InvWatch.lean`), `recvLoop` records
     `creq.PrevKv`, `sendLoop`'s branch `watch.go:442-455` (`watchable.Range` at `ModRevision - 1`).
   - Callers passing `prevKV = false` must see no change (watchkv, cachekv, linkv3p `MainWatch`, the
     compactor, `etcdstart.Collect`).
3. STOP (S2): report the statements and the config's trust-base effect.

## Handoff point (2026-11-13, end of the first 7f-5 agent's context): S1 reviewed; fixes next

S1 (`c46c52934c`) passed 81's axiom review with one MAJOR and minors. **Do these, in order** (81's
decisions, verbatim in the worktree's `questions.md`, last entry; review journal
`/root/.claude-csail/projects/-shared-etcd-grove/c04a65b0-a272-4ae4-94c7-91aa4a20ea30/subagents/workflows/wf_115e23d1-72c/journal.jsonl`):

1. **T5-c (MAJOR).** In `Proof/k8s_io/apiserver/pkg/util/feature/Gate.lean`, do not quantify the `Set`
   triple over every `b`. Add a table in the trusted text giving one fixed value per feature
   (`WatchList ↦ true`, every feature B5 covers ↦ `false`, e.g. `k8sSetValue : GoString → Option Bool`
   or two lists), and specify `Set(setArg s v)` only for `s` with its table value `v`. Then
   `featureOn`/`featureOff` of one feature are unreachable by construction (`featureSet g s v` for the
   one `v`). Restate the header's assumption: no other mutator runs; repeats of the same value are
   harmless. Drop "before any Enabled" if no triple needs it (none should). Callers to adjust:
   `noStreaming.lean`, `watchList.lean` (the side condition becomes the table lookup).
   Add `ResetFeatureValueToDefault` and `AddDependencies` to the mutator lists (Gate.lean header,
   freeze note S0.4, the grep). Make the closure check cover `examples/k8s/daemonset/dsmain` too, or
   state with evidence why it is outside. Turn the check into a script (e.g. `etc/featuregate-check.py`:
   `go list -deps` of the k8s examples, grep the mutators, compare to an allow-list with each hit's
   verdict) and wire it into `etc/gates.sh` (B5 has no gate today, as far as this agent saw; add one
   for both). The S0.4 grep command is in this agent's history: closure via `go list -deps -f` with
   GoFiles, regex over `DefaultMutableFeatureGate\.(Set|SetFromMap|OverrideDefault|SetEmulationVersion|Add)|\.SetFromMap(WithLogger)?\(|OverrideDefault(AtVersion)?\(|SetEmulationVersion|DeepCopyAndReset|featuregatetesting|ReplaceFeatureGates|AddFeaturesToExistingFeatureGates|DefaultMutableFeatureGate *=|DefaultFeatureGate *=`
   (hits saved in `/shared/tmp/k8s7f5/k8s-mutator-hits.txt`).
2. **T5-c docstring (minor 3).** Gate.lean's `Set` error branch says "changes nothing `Enabled`
   reads": inaccurate in Go (a failed `Set` stores the raw pair in `enabledRaw`, poisoning later
   `Set`s: `feature_gate.go:500-504`; `watcherctx` scenario `failed-set`). Reword (what is true: the
   map `Enabled` reads, `enabled`, is not stored; `enabledRaw` is).
3. **T5-a (minor 2).** Add grpc metadata's `copyOf` to the translation config (in the dry-run patch
   `/shared/tmp/k8s7f5/goose-dry-full.patch` for 7f-3a; no new trust). State the Lean result honestly
   ("parent's metadata plus one key": `strings.ToLower` is trusted to return some string), or fix it.
   Strengthen `examples/premisefix/watcherctx/requireleader_test.go`: a non-trivial `Cause` (a parent
   cancelled with `WithCancelCause(errX)`: the child's `Cause` is `errX`), and a NoAlias test that would
   fail without `Copy` (e.g. a parent `MD` whose `hasleader` key exists with another value, or check
   that writing the child's `MD` slice does not change the parent's).
4. **S0.1 (minor 4).** In `notes/k8s-7f5-freeze.md` §S0.1, add the row `getCurrentStorageRV(ctxRL)`
   (`watcher.go:146,193-209`; `store.go:240,735`: with RV 0, WatchList on and SendInitialEvents false,
   `getStartWatchResourceVersion` calls it on `ctxRL` before `createWatchChan`). Say that the strict
   control covers only RV > 0 with a fake watcher, and cite the reviewer's real-member recording test
   `/shared/tmp/coord-81/k8s7f5-review/clientkeys/keys_test.go` (or extend the control).
5. Rebuild (targeted, then the full build under flock and the cap), `etc/tcb-report.py --check
   --update` (one new axiom expected, `k8sfeature.featureOn_persistent`; report if it changes), the
   collections (`--collection etc/tcb-collections/k8setcd3.txt --check --update`; check all 55: the
   loop must not be cut by `head`), gates. Add an "S1 review" section to the freeze note (each finding,
   the fix). Add a STATUS entry (oldest moved to status-history's list, append only, `wc -l` check),
   noting the temporary premise of Q6 is not yet introduced (7f-5a). Merge lean, land via
   `etc/land.sh` on 81's go, report.

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
