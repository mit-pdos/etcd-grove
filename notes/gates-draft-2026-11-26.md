# Gate allow-list draft for the etcd_safe branches (2026-11-26)

DRAFT for the lead's review, not to land. Branch `etcd-safe-gates-draft/2026-11-26`, off `etcd-safe-f7-fork/2026-11-26`
@ `37fd5d261b` (the superset). Changes only allow lists and registries: `etc/mode-allow.txt`, `etc/mode-baseline.txt`,
`etc/errdesc-check.py` (`REVIEWED`) and `etc/model-param-allow.txt`. No Lean, Spec or axiom text.

The two trees:
- **T10**: `etcd-safe-t10b/2026-11-26` @ `9f2a8ff9ea` (built content `d053f13508`; fk-lean1 `~/eg/wt/etcd-safe-t10b`).
- **F7**: `etcd-safe-f7-fork/2026-11-26` @ `37fd5d261b` (fk-lean2 `~/eg/wt/etcd-safe-f7-rlog`).

Their four gate files were identical at those commits, except `etc/featuregate-allow.txt` (the examples' etcd pin).

## Result

| gate | entries | T10 | F7 |
|---|---|---|---|
| mode | 7 allow lines (29 findings) and 4 baseline rows | ok (487, baseline 487) | ok (481, baseline 487) |
| errdesc-check | 2 `REVIEWED` keys | ok | ok |
| model-param | 286 pair lines (108 T10, 178 F7) | ok, with the T10 subset (198 pairs) | ok (376 pairs) |
| featuregate | 3 lines re-pinned, T10 only | ok, with the T10 patch | ok as is (no change) |

## mode (`etc/mode-check.py`)

Every finding is `lit-mode` and in class `unmoved`. Each is the auth-on (or auth-off) twin of a row that is already
`unmoved`, and it moves with that row in the mode cleanup. The precedent is `ba18d01d55` (M1): it classified
`memberUp_req` as `unmoved` and raised the baseline from 456 to 457.

| entry (regex) | n | twin of (precedent row) |
|---|---|---|
| `etcdstart/Start.lean::(memberBuiltOnL\|memberUpOnL_intro\|wp_Start_builtOnL)` | 17 | memberBuiltL/memberUpL/wp_Start_builtL with auth on, as `memberUpOn` (etcdstart `Defs`) and `srvWOk_of_readOn` |
| `dist/MemberLessor.lean::memberUpOnL` | 2 | `memberUpOn`'s body verbatim, plus the lessor's name |
| `dist/server/MemberSplit.lean::(memberUpL_req\|memberUpOnL_req)` | 2 | `memberUp_req` (M1's row), with the lessor, and its auth-on twin |
| `dist/server/MainLogger.lean::MainLogger.wp_proof` | 1 | NewServer's post read as `memberBuiltOnL` (`bootKVOf true`) |
| `dist/AuthViewDist.lean::adminRepliedD` | 1 | `v3rpc.adminReplied`'s `adminDoneM true` (`api/v3rpc/AuthService.lean`, unmoved) |
| `etcdserver/NewServerCrash.lean::NewServer.specC` (T10 only) | 3 | `NewServer.specR` (the post word for word, at specR's auth-off scope) |
| `etcdserver/NewServerRAt.lean::NewServer.specRAt` (T10 only) | 3 | `NewServer.specR` / `wp_proofRG` |

**Baseline** (`etc/mode-baseline.txt`):

| row | was | now |
|---|---|---|
| `lit-mode …/examples/etcd/dist` | 0 | 3 |
| `lit-mode …/examples/etcd/dist/server` | 1 | 4 |
| `lit-mode …/examples/lib/etcdstart` | 11 | 28 |
| `lit-mode go_etcd_io/etcd/server/v3/etcdserver` | 276 | 283 |

The `etcdserver` row has 1 more on both trees: `AuthSrv.lean`'s `authSrvTPAt_off`, already classified `bridge` by the
`_off` name rule. T10 adds the 6 `NewServer` rows on top. One file passes both trees because each row takes the
higher tree's count. F7 then reports "277, down from 283", which is not a failure.

**FLAG (the ratchet).** The baseline "may only go down". These changes raise it by 30, from 457 to 487. This is the lead's
decision, as M1's raise was. The draft writes the rows by hand. `--check --update` on one tree would write that tree's
counts, so the 283 would be lost on F7.

## errdesc-check (`etc/errdesc-check.py`, `REVIEWED`)

| key | why it is true of Go (precedent) |
|---|---|
| `Spec/…/examples/etcd/dist/KVGetDist.lean` | `statusErrOk` in `KV_Get_dist`'s error arm only, a weakening of the proved `kv.Get.spec`'s `kvErr` (`InvKVConn.lean`: `clientErr ∗ statusErrOk ∗ errCellOk`, proved over the same translated clientv3 code). Across machines the error is still `toErr`'s: a grpc `*status.Error` (the `Error.lean` entry), an rpctypes `EtcdError` (the `rpctypes/Init.lean` entry) or a context error. |
| `Spec/…/examples/etcd/dist/WatchDist.lean` | `statusErrOk` in `RequestProgress_dist`'s post only, verbatim the proved `watcher.RequestProgress.spec`'s post (the same `watch.go`: `errors.New`, `ctx.Err()` or the stream's `closeErr`). `Watch_dist` names none of the predicates. |

Lean's own `KVGetDist.lean` does not mention `statusErrOk`; the T10/F7 weakening of `kvErr` added it. The evidence is
by precedent (the proved in-process specs), not a new Go test. A fresh `axiom` review would add a test.

## model-param (`etc/model-param-allow.txt`)

**Shape.** All 24 axioms have KV_Put_dist's exact shape in the gate's walk (read off each tree's
`.lake/model-param.jsonl`), and all but `New_user_dist` produce its 13 findings (12 rule 1, 1 rule 2):
- received keyed atoms: `grpc{Req,Rep}ModelOf` at `etcdInterceptorOk{,M}/{Req,Rep}`;
- supplied keyed atoms: the same registries at `grpcInvokerOk/{Req,Rep}`;
- the same eight service-table binder paths.

So each axiom gets N2's 12 entries (lines ~108-119), with the same paths and the same depositors: the axiom itself, or
`NewStream.wp_proof` for the stream registries. Each reason names the Go call and its Request/Response pair; each
axiom's docstring names the call.

**T10 (9 axioms, 108 lines; F7 has them too).**
- Unary, verbatim KV_Put_dist's:
  - `KV_Compact_dist` (Compaction{Request,Response});
  - `view.Lease_Grant_dist`, `view.Lease_GrantLive_dist` (LeaseGrant…);
  - `view.Lease_LeasesGranted_dist`, `view.Lease_LeasesLive_dist`, `view.Client_LeaseLeases_dist` (LeaseLeases…);
  - `view.Client_LeaseTimeToLive_dist` (LeaseTimeToLive…).
- Stream: `Watch_dist`, `RequestProgress_dist` (the Watch stream).

**F7 (15 more, 178 lines).**
- Unary, verbatim:
  - `authd.{KV_PutOn,KV_GetOn,KV_DeleteOn,Txn_CommitOn}_dist`;
  - `authd.Auth_{AuthEnable,RoleAdd,RoleGrantPermission,UserAdd,UserGrantRole}_dist`;
  - `authd.Lease_{GrantOn,LeasesOn,RevokeOn,TimeToLiveOn}_dist`.
- Stream: `authd.WatchOn_dist`.
- `authd.New_user_dist`: 10 lines.

**FLAGS (for the lead; I would allow all of them, but the wording has no direct precedent):**
1. **The stream axioms** (`Watch_dist`, `WatchOn_dist`, `RequestProgress_dist`): N2's wording ("the request model the
   axiom calls the interceptor contract with is X's") does not fit them, because they call no unary interceptor.
   Their reasons say instead:
   - the contract's `Req`/`Rep` (received in `isNewClient`) and the unary entries are inert in them;
   - whoever calls the contract passes a `Req` whose registration `grpcInvokerOk` requires (the axiom's own `supp` line);
   - the watch's stream entry is read by the `NewStream` of its name.

   The paths and depositors are N2's.
2. **`New_user_dist`** (a constructor: `clientv3.New` with a user name, returning `isNewClient`) has the polarity
   reversed. It supplies the atoms at `etcdInterceptorOk{,M}/{Req,Rep}` and receives them at `grpcInvokerOk/{Req,Rep}`
   (11 findings). Entries:
   - `grpcInvokerOk/{Req,Rep}`, depositor itself: in the returned interceptor contract, the invoker receives the `Req`
     its caller passed, whose registration the same contract requires of the caller (its own `supp` at
     `etcdInterceptorOk/Req`);
   - the 8 table paths as `bridge.New`'s (lines ~83-86): it reads no entry; unary entries are tied by `Invoke`, stream
     entries by `NewStream`.
3. The gate's depositor test is by name ("`D` supplies the registry, keyed"), so it cannot tell a right reason from a
   wrong one. The 286 reasons are for the lead to read. They were generated from one template per shape (unary,
   stream, constructor) with the Go call substituted.

**The two trees need different files.** The `authd.*` axioms are not walked on T10, so their entries are stale there
and fail ("not a walked trusted statement"). T10 takes the file truncated before the line `# F7's (etcd-safe-f7-fork)`:
`sed '/^# F7.s (etcd-safe-f7-fork)/,$d' etc/model-param-allow.txt`. Merging F7 into T10, or the other way, makes the
full file right.

## featuregate (T10 only; mechanical)

T10's examples pin etcd at `v3.0.0-20261125101634-251a430ce042`. Its `etc/featuregate-allow.txt` still names
`20261124070122-df6af0c36a6b` in the three `inert` lines of `github.com/upamanyus/etcd/pkg/v3/featuregate/feature_gate.go`
(etcd's own gate's definitions). The fix is the version string, not on this branch (F7's file already names F7's pin
`20261126150644-d26dd5da6f38` and passes):

    sed -i 's/20261124070122-df6af0c36a6b/20261125101634-251a430ce042/' etc/featuregate-allow.txt   # on T10

The hit lines' text is the same at the new pin, so the verdict ("etcd's own feature gate, its definitions") carries over.

## Commands run

- mode, errdesc (source only, local): `python3 etc/mode-check.py --check` and `python3 etc/errdesc-check.py`, in this
  worktree (F7), and in a `git archive 9f2a8ff9ea etc Spec Proof` copy with this branch's `etc/mode-allow.txt`,
  `etc/mode-baseline.txt` and `etc/errdesc-check.py` copied in (T10).
- model-param, on the builds, under `systemd-run --user --scope -q -p MemoryMax=20G python3 etc/model-param-check.py`
  with the allow file copied in and restored afterwards (`git status` clean after):
  - fk-lean1 T10 (`MODEL_PARAM_CACHE=~/eg/cache/model-param-cache`), the T10 subset: `ok (317 trusted statements
    walked, 43 registrations …, 309 finding(s) accepted by 198 pair entries, 26 selftests, 13 of 13 Lean runs from the
    cache)`;
  - fk-lean2 F7 (`LAKE_OPTS=--packages=.lake/package-overrides.json`), the full file: `ok (331 …, 502 finding(s)
    accepted by 376 pair entries, …, 16 of 16 Lean runs from the cache)`.

  Iterated locally first with `--json <that run's jsonl> --reuse`, which repeats the judging exactly.
- featuregate: fk-lean1 T10 with the patched file: `ok (66 mutator hits in 22200 Go files of 3 programs and 1
  outside …)`; fk-lean2 F7 unchanged: `ok (66 … 22197 …)`.
