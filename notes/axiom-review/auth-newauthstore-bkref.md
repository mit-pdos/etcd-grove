# Axiom review: `auth.NewAuthStore.wp_proof` over a `BkRef` with `authParams` (`cca7e9a4a9`)

- **Axiom**: `auth.NewAuthStore.wp_proof : auth.NewAuthStore.spec`
  (`Proof/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`), its statement in
  `Spec/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean`, as generalized by `cca7e9a4a9` (branch
  `mvcc-api`, strict M1): the backend `d : mvcc.KBReal` (parameters `mvcc.KBReal.P d`) became
  `d : mvcc.api.BkRef` with any parameters `d.P` meeting the new premise `auth.authParams d.P`
  (`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean:106-114`), which replaces the three premises
  `d.P.has mvcc.auth{,Users,Roles}BI`:
  ```lean
  def authParams (P : backend.BParams) : Prop :=
    ∀ bi ∈ [mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI],
      P.has bi ∧ P.HB bi.name = true ∧ P.SB bi.name = false ∧ P.RB bi.name = true ∧
        ∀ k, P.HK bi.name k = false
  ```
- **Revision**: the etcd fork `ce3dbc097f` (`.lake/go-src/etcd`, the pin of `etc/goose.py`);
  go1.27.3. The restated statement is not built (it imports `etcdserver.InvBoot`, red under strict
  M1: `notes/mvcc-migration/auth.md`), so it has not been elaborated; read as written.
- **Verdict: survives** (2026-11-05). No counterexample (no Go panic to prove away), none built.

## What the generalization adds

`KBReal.P d` (`Proof/.../storage/mvcc/InvStore.lean:105-111`) left `BT`, `hookMax` and `limit` free
(fields of `KBReal`) and fixed the rest for every bucket: `HB` all but `key`, `SB` only `key`, `HK`
the consistent index's two keys in `meta`, `RB` the rest buckets, `FV = metaRevVal`. `authParams`
keeps the three auth buckets' rows of these (for `auth`, `authUsers`, `authRoles`: `HB` true, `SB`
false, `RB` true, no `HK`; and `has`, as before) and leaves free **the other buckets' `HB`/`SB`/`HK`/`RB`
and `FV`**. Every old instance is a new one (`"auth"` is neither `key` nor `meta`, and is a rest
bucket); the new instances are backends whose other buckets are hook buckets, safe-range or
tracked differently, with other hook keys or another `FV`.

`d.P` occurs in the statement only in the pre, `backend.isBackend d.γB d.P W Pk d.b`. The post
(`bOpen`, `plHook`, `rbOwnIn d.γB S …`, `authBeOn stl d.b`, the reader slots, `isReqAuth`,
`authApplyOk`, `authRecoverOk`) does not mention it. So the new instances change nothing in what is
claimed; they widen which backends the claim is made about.

In Go, `P` is ghost except `limit` (`isBackend`'s `batchLimit ↦□ P.limit`) and `BT` (the Go
buckets' ids): `HB`/`SB`/`HK`/`RB`/`FV` are the backend proof's bookkeeping: which buckets the
pre-commit hook may write (`hooksSpec`/`hookStep`), which keys only the hook writes, which buckets
`rbPart` tracks, which values a compaction key takes. A different `P` in the pre therefore means
(i) a different pre-commit hook the caller can install (one whose contract `hooksSpec γ P` holds
at that `P`) and (ii) different ghost tracking of the other buckets. Both are attacked below.

## Attacks tried

1. **What `NewAuthStore` touches.** `NewAuthStore` (`server/auth/store.go:956-1004`) calls
   `be.CreateAuthBuckets()` (`storage/schema/auth.go:50-57`: `LockOutsideApply`, `UnsafeCreateBucket`
   of `Auth`, `AuthUsers`, `AuthRoles`, `Unlock`), `be.BatchTx()`, `tx.Lock()` (`auth.go:108`:
   `LockInsideApply`), `UnsafeReadAuthEnabled`/`UnsafeReadAuthRevision` (`UnsafeRange(Auth, …)`,
   `auth.go:123-144`), `commitRevision` (`store.go:1012`: `UnsafePut(Auth, "authRevision", …)`),
   `setupMetricsReporter` (no backend), `refreshRangePermCache` (`auth/range_perm_cache.go:131-153`:
   `UnsafeGetAllUsers`, `UnsafeForEach(AuthUsers, …)`, `auth_users.go:85-99`; `getMergedPerms` only
   per user, and there is none), `tx.Unlock()` (`auth.go:112-117`: the batch `Unlock`, then
   `Commit`) and `be.ForceCommit()`. No other bucket. The Go check below wraps the backend and its
   batch transaction and records every call: across 12 configurations the calls are exactly
   `Create:auth`, `Create:authUsers`, `Create:authRoles`, `Range:auth`, `Put:auth`,
   `ForEach:authUsers` plus the lock/unlock/commit calls. Every operation on a bucket is at an auth
   bucket, whose rows `authParams` fixes to `KBReal.P`'s.
2. **The post on other buckets.** It speaks of them only through `rbOwnIn d.γB S r'`, with `r'` equal
   to `r` off the auth buckets, idle on all of `S`. *Contents*: the code writes no other bucket
   (attack 1), and the hook cannot change a tracked bucket under any `P` (`hookStep`,
   `backend/Model2.lean:406-411`: `rbData P st'.S = rbData P st.S`). *Idle*: the backend's proved
   `batchTxBuffered.Unlock.spec` returns `rbOwnIn γ S r` for whatever part it is handed, at any `P`;
   the Go basis (`batch_tx.go:328-360`: the whole write buffer written back, a commit when a delete
   is pending) does not look at `P`. *Untracked names in `S`*: `rbPartF` forces `r` absent there, and
   `r'` agrees with `r` off the auth buckets. The Go check leaves puts pending in `key`, `lease`,
   `cluster`, `members` and a committed delete in `lease` before the call: afterwards a fresh
   `ConcurrentReadTx` and the batch transaction both see the contents from before the call on each.
3. **Does `authParams` exclude every parameter where the post is wrong?** Each conjunct, if
   dropped:
   - `has`: `UnsafeCreateBucket`/`UnsafePut` need it; `mvcc.authBI`/`authUsersBI`/`authRolesBI` are
     `⟨20, "auth"⟩`, `⟨21, "authUsers"⟩`, `⟨22, "authRoles"⟩`, schema's ids
     (`schema/bucket.go:52-54`). The buffers are keyed by id, and `isBackend`'s `P.Wf` makes `BT`
     injective, so no other name in the table can share an auth bucket's id. (`BT` was free before.)
   - `RB`: with `has`, it puts the bucket in the tracked names `γ.rbD` (the batch lock's `rbSide`,
     `backend/InvBackend.lean:643-645`). Without it, the bucket can be outside `γ.rbD` (`rbD` is the
     table's tracked buckets and `rbData`'s at creation). `rbPartF` would then force the post's `r'`
     to be absent at `auth`, while `r'` inserts `authBoot` there. The post would be unsatisfiable,
     and the axiom would prove any continuation, a panic included. `authParams` excludes this, and so did
     `KBReal.P`. The pre's reading "the auth buckets are empty" also rests on `rbPart` covering them.
   - `HK` false: `commitRevision`'s put needs no `hkOwn` (`hkPut`); a hook key in `auth` would
     mean only the hook writes it.
   - `SB` false: matches Go's `safeRangeBucket: false` for the three buckets.
   - `HB` true: as in `KBReal.P`.
   - `FV`: the compaction keys are `meta`'s two (`fkKey`, `Model2.lean:468`), so no auth put needs
     `FV`; leaving it free changes nothing here.
4. **A hook that only the new parameters allow.** At a `P` where, say, `lease` is a hook bucket and
   untracked, the caller can install a pre-commit hook that writes `lease`, which `KBReal.P` would
   forbid. The hook runs at every commit inside the call (3 to 7 times in the Go check, depending on
   the batch limit). `hookStep` at any `P` keeps the tracked buckets, the auth buckets among them,
   and the write buffer of every non-hook bucket. In the Go check the hook puts a counter in and
   deletes a key from `alarm`, `lease` or `members` at every commit. The auth buckets still end at
   exactly `{authRevision: 1}`, `{}`, `{}`, and every other tracked bucket is as it was.
5. **The batch limit and write-back tokens.** These do not depend on the new freedom (`limit` and
   `hookMax` were free before). For the record, Go makes two write-backs at any limit: the
   `Unlock`s of `CreateAuthBuckets` and of `authBatchTx.Unlock`. `Commit` and `ForceCommit` commit
   with `pending` reset to 0 before their own `Unlock` (`batch_tx.go:281-318, 362-366`), so they
   write nothing back. That matches the pre's `ownToks d.γB.wb 2`. The Go check runs at limits 1,
   2, 3 and 10000.
6. **The post's contracts at the new backend.** `isReqAuth` names no backend
   (`etcdserver/InvRequest.lean:2022-2035`). `authApplyOk` and `authRecoverOk`
   (`etcdserver/SnapRO.lean:101-106, 272-290`) are unchanged by `cca7e9a4a9` and still quantify over
   `mvcc.KBReal` backends. For a store made on a non-`KBReal` backend, `authApplyOk` applies at
   `d.b` only if the caller also holds `isBackend` there at a `KBReal`'s parameters, which needs a
   second `isMutex` on the same batch lock. No spec makes one. So these contracts gain no instance.
   (They are a usability gap for the server track, already recorded in
   `notes/mvcc-migration/auth.md`, not a soundness one.)
7. **Inconsistency in Lean.** `authParams` is a pure proposition over `BParams`. It is satisfiable
   together with `P.Wf` (`KBReal.P` meets both), and the change adds no opaque constant or law.

## Go check

The test is `/tmp/authbkref/authbkref_test.go`, its own module, which `examples/go.mod`'s `replace`
lines point at the pins. It is not committed. It runs `backend.New` with `BatchInterval = 1h`, a
`BatchLimit` in {1, 2, 3, 10000} and a pre-commit hook (`backend.NewHooks`) that writes `alarm`,
`lease` or `members`. Before the call it creates the other schema buckets and leaves writes behind
them (puts in `lease`, `key`, `cluster` and `members`, the last one only buffered, and a deleted
`lease` key). It then calls `auth.NewAuthStore(lg, schema.NewAuthBackend(lg, rec), tokenNop, 10)`,
where `rec` is a recording wrapper of the backend and its batch transaction. After the call it
checks four things:

- every recorded bucket operation is on an auth bucket;
- the store is disabled;
- a fresh `ConcurrentReadTx` and the batch transaction agree with the contents from before the call
  on every other bucket but the hook's and `meta`;
- the auth buckets are `{authRevision: 00…01}`, `{}`, `{}`.

```
=== RUN   TestNewAuthStoreOtherParams/1-alarm
    authbkref_test.go:197: limit=1 hook=alarm: calls [BatchTx Commit Create:auth Create:authRoles Create:authUsers ForEach:authUsers ForceCommit LockInsideApply LockOutsideApply Put:auth Range:auth Unlock]; hook ran 7 times; auth=map["authRevision":"\x00\x00\x00\x00\x00\x00\x00\x01"]
...
=== RUN   TestNewAuthStoreOtherParams/10000-members
    authbkref_test.go:197: limit=10000 hook=members: calls [BatchTx Commit Create:auth Create:authRoles Create:authUsers ForEach:authUsers ForceCommit LockInsideApply LockOutsideApply Put:auth Range:auth Unlock]; hook ran 3 times; auth=map["authRevision":"\x00\x00\x00\x00\x00\x00\x00\x01"]
--- PASS: TestNewAuthStoreOtherParams (0.02s)
    (12 subtests, all PASS)
```

## Not tried

- A Lean counterexample: there is no Go panic, and no instance whose post is unsatisfiable
  (attack 3).
- The parts of the axiom that `cca7e9a4a9` did not change: the auth-off contracts' truth, `Recover`,
  the reader slots, `authRecordsFit`, the token accounting beyond attack 5. `notes/audit.md`'s
  earlier "ok" covers them.
- The server track's restatement of `authApplyOk`/`authRecoverOk`/`InvBoot` over `BkRef` and
  `authParams` (`notes/mvcc-migration/auth.md`, "Follow"). It is not written yet. When it is, it
  needs the same review, because there the admin writes delete in the auth buckets and `SB`/`HK`
  of the auth buckets carry weight (both are fixed by `authParams`).
- Elaborating the restated statement (it is not built).
