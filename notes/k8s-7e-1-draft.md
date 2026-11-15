# k8s 7e-1: Draft (2026-11-10, branch `k8s-7e`; a HARD STOP for etcd-grove-81)

7e-1 discharges the three pending hypotheses of the closed `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`,
`k8s_etcd3_partition_safe` (and `_adequate`): `HGetAt` (`kubernetes.Client.GetAt.spec`), `HList`
(`kubernetes.Client.List.spec`) and `Hpl` (`k8s_etcd3.clientErrPlain`). It includes what was 7c-3:
the client chain at any revision, with the read errors' identity carried from the gRPC attempt.
Scope: `notes/k8s-7e-scope.md` §5 and §9; `notes/k8s-etcd3-plan.md` ("7c: Scope", "7c-1: Draft").
The survey behind this Draft read the client chain on k8s-7e after the merge of lean `d33293fe11`.

**Statement of the goal.** When 7e-1 is done, the three closed theorems have exactly lean's premises.
`Hpl`, `HGetAt` and `HList` are gone. No new axiom. The trust base changes only by the restatement in §4.

## 0. What exists (survey)

- **Server side, done (7c-2 part 2).** `etcdRangeSpecM` (`client/v3/KVServiceOn.lean:384`) gives the
  caller's error outcome `Ψe futureRevDesc` / `Ψe compactedDesc` from `rangeErrReply` (the read's log,
  `□ Q (kvStateOf log)` for a linearizable read, and `rangeFutureAt o log`:
  `len log - 1 < o.base.rev`). `handlerDescs = [futureRevDesc, compactedDesc]`.
  `grpcInvokerOk` (trusted) gives, at an attempt's error with `errDesc err ∈ handlerDescs`,
  `Ψe (errDesc err)`. `ctxErrClient` excludes `handlerDescs` from `ctx.Err()`.
- **Client side, dropped.**
  - `attemptPre` (`InvKVConn.lean:1278`) instantiates `Ψe := fun _ => True`.
  - The retry interceptor's proof (`Client__unaryClientInterceptor.lean:177,271`) discards the conjunct.
  - `etcdInterceptorOk`'s, `kvErr`'s and `rangeCallOut`'s error branches carry no description.
  - `rpctypes.Error` keeps `errDesc`. `ContextError.spec` does not state it, and neither do
    `waitRetryBackoff.spec` or `refreshToken.spec`.
- **Revisions.** `client_range_any`/`kv.Get.specM` take any option list. `rangeReplyOk` is stated at
  `stateAt log (rangeRev …)`, and `rangeAns_st` gives the answer at `σ.at (σ.readRev o.base.rev)`, but
  under `receiptBound GF ≤ 2^62`. `rangeReply_state_bnd`, which `Client.Get`'s proof uses, requires
  `o.base.rev = 0`: that is the only source of `Client.Get.spec`'s premise `opts.Revision' = 0`.
  `srvRangeOk_getKeyRev` (one key, any revision) exists. No lemma relates a range + limit + revision
  answer and its count to `pageKvsL`/`listRespIs`.
- **`List`** (Go, `client.go:59-73`) calls
  `KV.Get(ctx, start, WithRange(GetPrefixRangeEnd(prefix)), WithLimit(opts.Limit), WithRev(opts.Revision))`,
  with `start = opts.Continue` if it is set, else `prefix`. It copies `Kvs`, `Count` and
  `Header.Revision`. It has no prophecy, and no patch for one exists.
- **`clientErr`** (`client/v3/ClientErr.lean:32`) is a leaf with the `EtcdError` `As` facts. No statement
  fixes the error's dynamic type. So `clientErrPlain` (`∀ ii, clientErr (ok ii) → typeSetContains
  ii.ty APIStatus.ty = false`) is **not derivable**: a leaf with a `Status()` method satisfies
  `clientErr`.
- **Callers of `Client.Get.spec`.** Only `store__Get`, `store__getCurrentState` and
  `store__GetCurrentResourceVersion`, all at revision 0. `Client.GetAt.spec` and `Client.List.spec` are
  used only by `store__getList` and by the driver's linking files.

## 1. Finding: `HGetAt`/`HList`'s error clause cannot be proved as stated (a soundness-of-premise finding)

Both hypotheses' error branch is `rangeErrSound o Q err`:
`□ (⌜errDesc err = futureRevDesc⌝ -∗ ∃ σ, □ Q (W64 σ.rev) σ ∗ ⌜σ.rev < o⌝)`.
That is, the read update fired at `σ` **with its revision argument equal to `σ.rev`**.

- The client makes its read update once, at the prophesied response revision `R` (D30n:
  `∀ R, |==> □ … kvReadAu (Q R)` is used once).
- On the error path the prophecy is never resolved. The client cannot resolve it either: an error has
  no header, so the served revision is unknown to it.
- So at an error, the update fired at some `σ` gives `□ Q R σ` for an `R` unrelated to `σ.rev`.

`rangeErrSound` as written is therefore not implementable by any client proof of this design. Today the
closed theorems take it as a hypothesis. `HGetAt`/`HList` may be unsatisfiable, which would make the
theorems vacuous.

**Fix (recommended, R1).** The error clause quantifies the revision argument:

```
rangeErrSound o Q err := □ (⌜errDesc err = futureRevDesc⌝ -∗ ∃ R σ, □ Q R σ ∗ ⌜σ.rev < sint.nat o⌝)
```

The consumers follow:
- the store's `listReadError`/`getList` (7e-2's statements: `readErrIs`'s future clause, the same
  change);
- the driver's read updates (7e-4's `InvSteps`): `readQ`/`listQ` commit an `ETooLarge` answer at `σ`
  whenever the driver's own prophecy of its answer says `ETooLarge` and `σ.rev < n`, whatever `R`.
  Their commit for an answered read stays `σ.rev = R`.

These are internal statements of the store and the driver, so no closed statement changes. They are
changes to 7e-2's and 7e-4's approved statements, though, so 81 decides. To check before Lean: that
the driver's `kInv` lets an `ETooLarge` commit happen at a state picked by the update alone (it does
for the Get's `ETooLarge` today: committed at `R` because `readQ`'s bit is `σ.rev = R`; the change
moves that commit to the `σ.rev < n` condition).
**Alternative (R2):** keep the error clause and add a client-side ghost resolution. This is not
possible: a prophecy patch may only resolve read-only expressions, and the client has no revision
on the error path.

## 2. The client chain at a revision, with the read error's identity (was 7c-3)

All of these are proved statements of the client package. None is trusted.

1. **`attemptPre`** takes the caller's `Ψe` (persistent, since retried attempts reuse it):
   `attemptPre … Spec m Φ Ψe := ∀ md, ⌜clientAttemptMd conn ctx md⌝ -∗ Spec md m Φ Ψe`.
   Every current user passes `fun _ => True` (mechanical).
2. **`etcdInterceptorOk`** (the retry interceptor's contract) gains an error outcome on its error side:
   `⌜errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)`. Its proof covers four ways the error is made:
   - the last attempt's error comes from `grpcInvokerOk`'s conjunct, no longer discarded;
   - `waitRetryBackoff`'s `contextErrToGRPCErr(ctx.Err())` has `errDesc ∉ handlerDescs`:
     `waitRetryBackoff.spec`'s post gains `errDesc err = errDesc ctx.Err()` (or directly `∉
     handlerDescs`), and `ctxErrClient` gives the exclusion;
   - `refreshToken`'s `gtErr` happens only after `shouldRefreshToken` returned `true`, that is, for
     `lastErr ∈ refusalDescs` (D29). To check in Lean: whether every k8s path rules this out (D29's
     `noRefusal` for an auth-off member). If not, `refreshToken.spec`'s post gains
     `errDesc gtErr ∉ handlerDescs` (Authenticate's errors). Authenticate's spec is plain and says
     nothing of its descriptions, so this second form would need a new fact. **If neither works,
     STOP:** report to 81.
   - `ContextError` (twice in `kv.Get`/`kv.Do`) returns `err` or `ctx.Err()`. Its post gains
     `errDesc err' = errDesc err ∨ errDesc err' ∉ handlerDescs`.
3. **`rangeCallOut`'s/`kv.Get.specM`'s/`client_range_any`'s error branch** gains
   `rangeErrOut ms c F o Q err`:

   ```
   □ ((⌜errDesc err = futureRevDesc⌝ -∗ ∃ x, ⌜x ∈ ms⌝ ∗ rangeErrReply x.E x.γr c F o Q (rangeFutureAt o)) ∧
      (⌜errDesc err = compactedDesc⌝ -∗ ∃ x, ⌜x ∈ ms⌝ ∗ rangeErrReply x.E x.γr c F o Q (rangeCompactedAt o)))
   ```

   Both halves are stated (7c's soundness). The k8s consumers use the future half only (B4). Callers
   of these lemmas that destructure the error branch (`examples/etcd/txnlin`, `compactwatch`,
   `goose/prophkv`, the k8s compactor, linkvtxn's `client_Get_*`) get one more conjunct to drop. This is
   a mechanical change; the Draft-stage count with `etc/importers.py --uses` is in §6.
4. **`rangeReply_state_at`** (new lemma, replacing the revision-0 `rangeReply_state_bnd` in `Client.Get`'s
   proof): `rangeReplyOk … o … Q m ⊢ ∃ σ, □ Q σ ∗ ⌜srvRangeOk o (σ.at (σ.readRev o.base.rev)) m ∧
   m.count = srvCount … ∧ m.hdr.revision = σ.rev ∧ σ.readRev o.base.rev ≤ σ.rev ∧ kvRevFits σ.rev⌝`.
   It must not need `receiptBound GF ≤ 2^62`: that would be a new bound premise, and could reach a
   closed theorem (`rangeAns_st` needs it; `rangeReply_state_bnd` does not). If it cannot be avoided,
   STOP.
5. **`rangeErrSound_of`**: `rangeErrReply … (rangeFutureAt o)` with `Q := Q R` gives
   `∃ R σ, □ Q R σ ∗ ⌜σ.rev < o⌝` (with `σ := kvStateOf log`; for a linearizable read only; the
   driver's reads are linearizable, `serializable = false` in `opGetModel`).

## 3. The kubernetes client's specs

### 3.1 `kubernetes.Client.Get` (restated; `Client.GetAt.spec` deleted)

Two specs of one Go function break the layout. Recommended: restate `Client.Get.spec` at any revision
and delete `Client__GetAt.lean`. `store.getList` then takes `Client.Get.spec`, with `Q` ignoring the mod
revision. Changes to the old text:

- The premise `opts.Revision' = W64 0` becomes `0 ≤ sint.Z opts.Revision'`.
- The success branch:
  `□ Q (W64 σ.rev) (modAt key (σ.at (σ.readRev opts.Revision'))) σ ∗
   ⌜resp.Revision' = W64 σ.rev ∧ σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev ∧
    ∀ v ∈ σ.kvs, v.value.length ≤ etcdKeyMax⌝ ∗
   kvOut resp.KV' (mvcc.findKey key (σ.at (σ.readRev opts.Revision')).kvs)`.
  The prophecy's second value becomes the key's mod revision **at the read revision**. The patch already
  resolves `resp.KV.ModRevision`, which is that value, so the patch is unchanged.
- The error branch adds `rangeErrSound opts.Revision' (fun R σ => ∃ m, Q R m σ) err` (R1's form).

At revision 0 the old answer is recovered: `σ.readRev 0 = σ.rev` and `σ.at σ.rev`'s key-values are
`σ.kvs`. A lemma `KVState.at_readRev_zero` is needed, if it is not already there. The three store
callers are re-proved at revision 0. Their statements are unchanged.

### 3.2 `kubernetes.Client.List` (proved; the hypothesis's text, with R1's error clause)

The statement is today's `Spec/go_etcd_io/etcd/client/v3/kubernetes/Client__List.lean`. Its premises
(key lengths, `0 ≤ Revision`, `0 ≤ Limit`, continue key empty or under the prefix) and its success
branch (`□ Q (W64 σ.rev) σ`, `σ.readRev opts.Revision' ≤ σ.rev ∧ kvRevFits σ.rev`, `listRespIs resp σ
pfx true opts.Revision' opts.Limit' start`, with `Kvs` owned) are kept. The error branch is R1's.
The vocabulary (`listRespIs`, `pageKvsL`, `rangeErrSound`) moves down from the store's `ListDefs.lean`
to `client/v3/kubernetes/Defs.lean` (Scope §5 asks for this move). The store imports it from there.

- **Prophecy patch** `etc/proph-patches/etcd/02-client-list-revision.patch`: `p := primitive.NewProph()`
  first, then `p.ResolveU64(uint64(resp.Revision))` before the success `return`. `etc/prophcheck`
  checks it. Re-translate with `etc/goose.py --project etcd`. This patch is not trusted text, but it
  changes the translated program, so it is listed here.
- **Proof.** `GetPrefixRangeEnd`, `WithRange`/`WithLimit`/`WithRev` (specs exist), then `client_range_any`
  with `[withRangeM (prefixRangeEnd pfx), withLimitM lim, withRevM rev]`, then `rangeReply_state_at`
  (§2.4). The new pure lemma `srvRangeOk_page`: `srvRangeOk` of a range `[start, prefixRangeEnd pfx)`
  with limit `l` at a store `s`, and `srvCount`, give `pageKvsL s pfx true start (limN l)`. This needs
  `start` under the prefix, and `kInScope pfx true k ↔ start ≤ k < prefixRangeEnd pfx` for such keys.
- **Risk: `Kvs` owned.** `listRespIs` requires `resp.Kvs' ↦* ps` (the store's `appendChunk` writes
  `kvs[i] = nil`, 7e-2's requirement). The reply's `rangeRespMsg` (`#Hsl2` in `Client.Get`'s proof) is
  persistent (`↦*□`). Owning it requires the decoded reply's `own` (`ProtoMsg.own`) to be carried from
  the last attempt through the retry interceptor and `kv.Do` to `kv.Get`'s post. That is a strengthened
  success post of the chain in §2 (proved statements). If the trusted attempt contract hands out only
  the persistent view, **STOP**: it is a trust question. Alternative: `appendChunk`'s write
  `kvs[i] = nil` takes only `↦*□`... impossible, since a write needs ownership.

## 4. `clientErrPlain`: the client error's dynamic type (a trust-base restatement)

`clientErr` gains one conjunct, the error's dynamic type in a fixed list:

```
clientErrTys : List go.GoType :=
  [PointerType grpc.internal.status.Error.ty, rpctypes.EtcdError.ty,
   PointerType errors.errorString.ty, context.deadlineExceededError.ty]
clientErr err := … ∧ ∀ ii, err = .ok ii → ii.ty ∈ clientErrTys
```

`clientErrPlain` then becomes a lemma of the driver: by cases on the list, with `go_type_set` for each
type. None of the four method sets (`[Error, GRPCStatus, Is]`, `[Code, Error]`, `[Error]`,
`[Error, Temporary, Timeout]`) has `Status`. It moves out of the closed theorems.

**What changes in the trust base** (restated, no new axiom; each statement attacked with the `axiom`
skill before the Freeze, as Q7c-2):
- `grpcInvokerOk` (inside the trusted `grpc.ClientConn.Invoke.spec`): an attempt's error is a
  `*status.Error` (grpc-go's `toRPCErr` and `status.Error`; the claim needs the attack to look at
  per-RPC credentials, the balancer's `ErrNoSubConnAvailable`, and compression errors);
- `cliStreamErr`, `client.eofOk` (`InvGrpcStream.lean`): status errors, and `io.EOF` (`*errorString`).

`ctxErrs`/`ctxErrClient` is a premise given by the context's owner, not trusted: `ctx.Err()` is
`Canceled` (`*errorString`) or `deadlineExceededError`. Its producers are re-proved; `Background()` never
errs.

The proved producers follow:
- `rpctypes.Error` returns an `EtcdError` value or `err`;
- `ContextError` returns `err` or `ctx.Err()`;
- `contextErrToGRPCErr` returns `status.Error`. `status.Error`'s spec (an axiom, `grpc/status/Error.lean`)
  must state the type. **This is a restatement of a trusted spec**, in this section's list.

A narrower form, the conjunct only on the paths k8s uses, does not save the restatement: the type
comes from the trusted attempt contract either way. The conjunct in `clientErr` itself is the least
churn, since consumers project and producers prove one more conjunct.

**Go test (before the Freeze):** `examples/k8s/etcd3` gains a test that drives the client through
partitions, a closed client and a deadline, and checks that every error `Client.Get`/`List`/
`OptimisticPut`/`OptimisticDelete` returns has one of the four dynamic types (`%T`). The trusted claim
is about every run, so the test is evidence, not proof; the axiom attack is the review.

## 5. Premises and trust base at the end

- **Closed theorems:** `Hpl`, `HGetAt` and `HList` are removed. They end with lean's premises. No new
  premise.
- **New axioms:** none.
- **Restated trusted statements:** `grpcInvokerOk`'s error type, `cliStreamErr`, `eofOk`,
  `status.Error.spec` (§4). `handlerDescs` is unchanged.
- **New program text:** the List prophecy patch (§3.2).
- **Changed approved statements (not closed):** `rangeErrSound` (R1), `readErrIs`'s future clause, the
  driver's `readQ`/`listQ` `ETooLarge` commit, `Client.Get.spec` (§3.1), `store.getList.wp_proof`'s
  callee (`Client.Get.spec` in place of `GetAt`).
- **Possible STOPs while proving:** §2.2 (`refreshToken`'s error), §2.4 (`receiptBound`), §3.2 (owned
  `Kvs`).
- **Interface files:** none of client/v3, kubernetes, the etcd3 store or the driver is API-listed.
  `interface/` changes only if `etcdstart`'s `isNewClient` changes; it does not.

## 6. Size and order

| Step | Content | Lines (est.) |
| --- | --- | --- |
| 1 | Go: the error-type test (§4); a List-at-revision Go test (past revision, future revision error) | Go ~150 |
| 2 | R1 in the store and the driver (`rangeErrSound`, `readErrIs`, `readQ`/`listQ`), built | 150-300 |
| 3 | `clientErr`'s conjunct; trusted restatements; producers; `clientErrPlain` lemma; axiom attacks | 200-300 |
| 4 | §2: `attemptPre`'s `Ψe`, the interceptor's error outcome, `ContextError`/`waitRetryBackoff`, `rangeErrOut`, callers' mechanical edits | 300-500 |
| 5 | §3.1: `Client.Get` restated and re-proved; three store callers; `getList` on `Client.Get` | 150-250 |
| 6 | §3.2: the patch, re-translation, `srvRangeOk_page`, `Client.List` proof, owned `Kvs` | 300-500 |
| 7 | Link (`Client__List` and `Client__Get` real; pending lines go), Results/Adequacy without the three, full build, tcb collections, gates | 100 |

In all, about 1200-1950 Lean lines. Checkpoints: after 2 and 3 (the trust restatements' attacks: a
hard stop), and after 7 (the Freeze with 7e-4's package, landed together).

## 7. Decisions asked of etcd-grove-81

1. **R1** (§1): `rangeErrSound` quantifies the revision argument, and the driver's `ETooLarge` commit
   moves to `σ.rev < n`. Recommended. Also: is the finding that `HGetAt`/`HList` as stated are
   unprovable (the closed theorems on k8s-7e may be vacuous until fixed) to be recorded in `notes/`
   (a bug in our own specs)? Recommended: yes.
2. **§3.1**: restate `Client.Get.spec` at any revision and delete `Client.GetAt.spec`. Recommended.
3. **§4**: `clientErr` gains the dynamic-type list, with the four trusted restatements (attacked
   before the Freeze) and the Go test. Recommended.
4. **§3.2**: the List prophecy patch. Recommended.
5. The order in §6. Recommended.
