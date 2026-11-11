# premise-fixes-8c handoff (client half: C1, C2, C3)

Scope: `/shared/tmp/premise-fixes-8/scope.md` (approved, "## Decisions"). Coordinator: etcd-grove-81.
Worktree `/shared/etcd-grove-pf8c`, branch `premise-fixes-8c` (cut from lean `da225483c9`). The
server half (S1/S2) is in `/shared/etcd-grove-pf8`; don't touch its files.
Decisions and forms: `questions.md` (worktree root, untracked).

## C1 contents

- C1 (trust change, approved):
  - `Proof/context/LibKeysChain.lean`: `metadata.outgoingCtxOkC` (Perennial's `ctxValue` at
    `mdOutgoingKey{}`) and its laws `_background`, `_todo`, `_from`, `_valueCtx`, `_ownKey`, `_raw`,
    `_todoFrom`, `_bgFrom`, `outgoingCtxOk_of_C`, `context.keyEqOk_of_ty_ne`.
  - Stronger posts: `WithCancelTodo` (+ `ctxValueFrom todoCtxVal ctx'`), `WithTimeoutBackgroundMd`,
    `WithRequireLeader` (inner triple), `AppendToOutgoingContext` (+ `outgoingCtxOkC`).
  - `wait.channelContext.Deadline` spec + proof (translated; for C3's `chanCtx_ok`; not linked yet).
  - Go tests `examples/premisefix/ctxvalue/clientctx_test.go`: `TestClientCallCtxPanics` (the
    scratch file's four contexts, Invoke and NewStream, plus a `withVersion` copy) and
    `TestClientContexts`. Pass.

## C1: LANDED

lean `f808e61706` (2026-11-11; gates all passed, `/shared/tmp/premise-fixes-8c/land-c1.log`). The
four trusted texts and the three forms were approved by etcd-grove-81 (`questions.md`).

## C2 (the cascade; no trust change): in progress

Done (commits `00aff9fc2c`, `4e7ccba3ff`; every module listed builds with a targeted `lake build`):
- The 11 contracts (`cache/v3/InvEtcd.lean`, `InvEtcdTxn.lean`, `InvEtcdTxnOwn.lean`) take
  `context.isContext ctx cs ∗ metadata.outgoingCtxOkC ctx ∗ ...` (the new conjunct right after
  `isContext`). `InvEtcd` imports `Proof.context.LibKeysChain`.
- The real client's proofs of them (`client/v3/{LeaseClient,ServerWatcher,ServerKVGet,KMGet,KMWatch}`):
  intro pattern `⟨#Hctx, -, ...⟩` (C2 doesn't use the fact; C3's `ctxOk` will). `client/v3/Results` builds.
- The cache: `Cache.get`, `Cache.serverRevision`, `Cache.Get` (exported API) and
  `conditionalProgressRequestor.run` take `outgoingCtxOkC ctx`; `isCacheFields`' `HisICtx` carries
  `outgoingCtxOkC cf.ictx` (`newCache`: `wp_WithCancel_Background`'s `ctxValueFrom`, then
  `metadata.outgoingCtxOkC_bgFrom`). `cache/v3/{Link,Results}` build.

Next, in order:
1. `examples/etcd/cache/Main.lean:755` (`wp_CGet` at `gctx` = `WithTimeout(Background())`) needs
   `outgoingCtxOkC gctx`. Plan (form-only: a stronger post on a proved spec): add
   `∗ _root_.Perennial.context.ctxValueFrom context.backgroundCtxVal ctx'` to
   `Spec/context/WithTimeoutBackground.lean`'s post (proved in `Proof/context/WithTimeoutBackground.lean`:
   name the dropped `-` of `wp_WithTimeout_Background`'s post and frame it), carry it into
   `client.wp_WithTimeout_bg`'s post (`TimeoutCtx.lean`, as `metadata.outgoingCtxOkC ctx'` via
   `outgoingCtxOkC_bgFrom`), then fix the `icases` patterns of their users (`etc/importers.py --uses
   WithTimeoutBackground.spec --files Spec/context/WithTimeoutBackground.lean`; 47 files mention it;
   `wp_WithTimeout_bgMd` too). Then `examples/etcd/cache/Results`.
2. The remaining direct users of the contracts, in this order (`/shared/tmp/premise-fixes-8c/c2-users-ordered.txt`):
   `examples/etcd/partition/MainWatch`; concurrency (`InvMutex.isEtcdMutexClient`, `InvSTM` 347/440,
   `InvSession.isSession`'s `ctx` (it is `WithCancel(pctx)`: Perennial's `wp_WithCancel` gives
   `ctxValueFrom pctx ctx'`, so `NewSession`'s pre takes `outgoingCtxOkC pctx` and `isSession`
   stores `outgoingCtxOkC ctx` by `outgoingCtxOkC_from`), `Election__*`, `Mutex__*`, `stm*`,
   `waitDelete(s)`); recipes (`InvRecipesClient`, `KVOfServer`, `waitEvents`, `Vertical`, `Results`);
   leasing (`InvLeasingKV` 229/259/300/398, then its 13 proofs).
3. Then the second ring: the specs whose callers pass a context into the above (Scope C.3: concurrency
   ~20, leasing ~24, recipes ~15, `client/v3/kubernetes` 5, v3lock/v3election 8, the k8s chain, the
   examples' `Main`s: `watch`, `auth`, `compactwatch`, `partition`, `txnlin`, `leasecatchup`, `restart`,
   `k8s/compactor`, `k8s/etcd3`, `lib/etcdstart`, `lib/cluster3`). Producers: `client.Ctx()` is
   `WithCancelTodo`'s context, whose post now gives `ctxValueFrom todoCtxVal` (C1) -> `isNewClient`
   should store `outgoingCtxOkC` of it (`newClient.lean:87` drops it as `-` today) via
   `metadata.outgoingCtxOkC_todoFrom`; `TODO()`/`Background()` by `_todo`/`_background`;
   `channelContext` by `_raw` (`chanCtx_libCtxOk` gives the WP form; type not in `valueSpecialTypes`).
4. Full build under the lock, tcb --check (no change expected), collections, interfaces (the cache's
   and concurrency's are not under `etc/api/`; regenerate the five that are only if they move),
   gen-init --check; STOP before land.sh.
5. C3 (Scope C.2 items 1-7; STOP on the exact "no AfterFunc" text), with `WithCancelValCtx`'s post.

Tools: `/shared/tmp/premise-fixes-8c/lb.sh FILE...` (a targeted `lake build` of files, errors only,
under the 64G cap; full log `/shared/tmp/premise-fixes-8c/lb.log`). Do not run several
`etc/lean-check.py` files at once on a cold import tree: parallel `lake setup-file`s raced and lost
`.olean`s (`BaseApply.olean` missing); `lb.sh` is reliable.

## Pitfalls

- Adding a conjunct to an axiom's post breaks `icases` patterns of its users: grep for the
  `wp_apply ... as` lines (`newClient`, `TimeoutCtx.wp_WithTimeout_bgMd`, auth `reqCtx`/`Work`).
- `ctxValue` needs `[context.Assumptions]`; `outgoingCtxOkC_ownKey` needs
  `[google_golang_org.grpc.metadata.Assumptions]` (struct key equality).

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json`
(TMPDIR=/shared/tmp). Single files: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py FILE`.
