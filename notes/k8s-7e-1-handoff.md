# k8s 7e-1 handoff (2026-11-10, branch `k8s-7e`, worktree `/shared/etcd-grove-k8s7d`)

Read first: `notes/k8s-7e-scope.md` §5, §9; `notes/k8s-7e-4-handoff.md`; `notes/k8s-7e-2-handoff.md`;
`notes/k8s-etcd3-plan.md` ("7c: Scope", "7c-1: Draft"). Rules: `/shared/tmp/coord-81/common-rules.md`.
Scratch: `/shared/tmp/k8s7e1/`. Coordinator: etcd-grove-81. Never push, never run `etc/land.sh`.

**What 7e-1 is.** The client chain at a revision (what was 7c-3), `kubernetes.Client.List` and
`Client.GetAt`, and the discharge of `clientErrPlain`. The closed `k8s_etcd3_safe`, `cluster_safe`,
`partition_safe` (and `_adequate`) on k8s-7e carry three pending hypotheses: `Hpl` (`clientErrPlain`),
`HGetAt`, `HList`. **k8s-7e does not land until 7e-1 proves all three**, so that the closed theorems
end with exactly lean's premises.

**The 7e-4 Freeze package** (`a3aa853a85`, full build green, 13783 jobs) was **reviewed and accepted by
etcd-grove-81** (2026-11-10). It is landable only together with 7e-1, because of the pending hypotheses.

## Steps (etcd-grove-81's list)

1. Merge lean (`d33293fe11`: stage A per-type protobuf/gRPC, premise fixes 1 and 3) into k8s-7e, full
   build, commit. Conflicts resolved with lean's model:
   - `Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdRequest.lean`: both changes (7e-2's
     `utf8Valid` premises, premise fixes 3's `statusErrOk err` precondition); the store's call sites
     take both (`Hutf.1 Hutf.2`, then `· iexact Hse` from `statusErrOk_split`); `store.getList`'s two
     calls (7e-2's) gain the same split of `Client.GetAt`'s/`Client.List`'s error posts.
   - `MainLinked`/`Results`: lean dropped `[Float64ToInt64Semantics]` (premise fixes 1); ours keep
     the pending hypotheses. `Link.lean` regenerated (`etc/gen-link.py --k8setcd3`).
   - tcb baseline and collections: union, then `etc/tcb-report.py --check --update` after the build.
2. Bounds gate: seven new `spec-thread` matches allowed in `etc/bounds-allow.txt` (decided by
   etcd-grove-81): the store's `New`/`GetList`/`getList`/`pagedChunks` (7e-2) and the driver's
   `call`/`Apply`/`Check` (7e-4). `etc/bounds-check.py --check`: ok (384).
3. This file records the acceptance of the 7e-4 Freeze package (above).
4. The 7e-1 Draft (`notes/k8s-7e-1-draft.md`): written, a HARD STOP; no Lean proofs past it until
   etcd-grove-81 decides its §7. Key points: (a) **finding**: `HGetAt`/`HList`'s error clause
   (`rangeErrSound`: `□ Q (W64 σ.rev) σ`) is not provable by the prophecy design (the prophecy is never
   resolved on the error path), fix R1 quantifies `R`; (b) `Client.Get.spec` restated at any revision,
   `GetAt.spec` deleted; (c) `clientErr` gains a dynamic-type list (trusted restatements of
   `grpcInvokerOk`, `cliStreamErr`, `eofOk`, `status.Error.spec`), making `clientErrPlain` a lemma;
   (d) a List prophecy patch; possible STOPs: `refreshToken`'s error, `receiptBound`, owned `Kvs`.

## Next, in order (after 81's decisions)

The Draft's §6 table, steps 1-7.

## Follow-ups (recorded, not in 7e-1)

- **`threadTok` through the owner** (decided by etcd-grove-81 with the allow-list entries): the store
  (`isStore`, built by `New`) should hold `collectorMux`'s reader-slot bound (`threadBound GF ≤ 2^30-1`)
  once, so that `GetList`/`pagedChunks`/`getList` and the driver's `call`/`Apply`/`Check` take only
  `threadTok` and the store's handle (`notes/bounds-plan.md`); then the seven allow-list entries go.

## Builds

Full (under the lock and the 64G cap; filtered log): `/shared/tmp/k8s7e1/full.sh LOGNAME`.
Targeted, capped: `/shared/tmp/k8s7e1/build.sh LOGNAME targets...`.
Every lake command takes `--packages=/shared/tmp/manifest-ddc.json`.
