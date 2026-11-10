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

## Draft review (etcd-grove-81, 2026-11-10): all five decisions approved (see `questions.md`)

Decision 3 is conditional: the Go error-type test and an axiom-skill attack on each of the four trusted
restatements come BEFORE building on them; a fifth error type is a STOP. The three possible STOPs stay.
Checkpoints: (i) R1 built (targeted green); (ii) Go test and attack results; (iii) Freeze package.
The finding is recorded in `notes/k8s-etcd3-plan.md` ("Bug in our own specs: `HGetAt`/`HList`'s error
clause unprovable").

### The check before R1: kInv allows the ETooLarge commit at a state the update picks (done: yes)

- A read changes no state; its commit is `getCall`/`listCall`'s one-shot commit bit (`γc`, own → discard)
  taken inside `get_read_au`/`list_read_au` while `kInv` is open at the firing state `σ`: `linU` becomes
  `contAt g0 x (kStep … x (c.abs σ)).2` (`lOut x σ` for a list). `kInv` constrains only that the model
  step is taken at the current state (`KOk`), not which firing commits.
- `Apply`'s prophecy's first value is the output's error kind (`xs.head?`, `resolve3`), known before the
  call. When it says `ETooLarge`, the answer is `ETooLarge`, and at any firing with `σ.rev < n`
  (`n = parseRVD x.MinRV'`) the model step answers `tooLargeL` (Get: `Inv.lean:288`; list: `lOut`,
  `Inv.lean:172`). So the commit at the first such firing is consistent with the final answer, whichever
  attempt fires first.
- If the call answers `ETooLarge`, some firing had `σ.rev < n`: from the client's error (R1's `∃ R σ, □ Q R σ ∗
  σ.rev < n`) or from a data answer at `R < n` (the store's own minimum check: the firing at `σ.rev = R < n`).

### R1, the implementation plan (step 2 of the Draft's §6; DONE, `3303ac0745`, checkpoint (i))

1. `ListDefs.lean`: `rangeErrSound o Q err := □ (desc = futureRevDesc -∗ ∃ R σ, □ Q R σ ∗ ⌜σ.rev < sint.nat o⌝)`;
   `readErrIs`'s future clause the same. Then `store__listReadError`, `store__getList` (the two
   `iunfold rangeErrSound at Hrs`, lines ~140, ~179), `pagedChunks`, `GetList` as they consume it.
2. Driver: `readQ`/`listQ` take the commit condition as a parameter, `cond : w64 → KVState → Prop`
   (`fun R σ => σ.rev = uint.nat R` for an answer, `fun _ σ => σ.rev < uint.nat n` when the prophecy says
   `ETooLarge`); `getCall`/`listCall`'s committed disjunct records `⌜cond R σ⌝` in place of `σ.rev = R`;
   `get_read_au`/`list_read_au`/`get_maker`/`list_maker`/`getCall_take`/`listCall_take` follow; `Apply`
   splits the answering case on `xs.head? = some tooLargeCode`. The answer `y = tooLargeL` matches
   `kStep`/`lOut` at the committed `σ` by `σ.rev < n`.
3. Targeted build (checkpoint (i)): the store's `Link`, the driver's `Link`/`Results`.

### R1 as built (`3303ac0745`; targeted builds green: the store's `Link`, the driver's `Link`/`Results`/`MainLinked`/`Adequacy`, every leaf importer)

- Store: `rangeErrSound`, `readErrIs`'s future clause, `listReadError`'s post, `pagesOk`'s error clause:
  `∃ (R : w64) σ, □ Q R σ ∗ ⌜σ.rev < …⌝`. `GetList`'s post: `∃ (R' : w64) σ, □ Q R' σ ∗
  ⌜σ.rev < uint.nat n ∨ R' = W64 σ.rev⌝ ∗ (the same tree)` (a too-large answer has `σ.rev < n`, since
  `listRevL ∈ {0, n}`; an answer has `R' = σ.rev`).
- Driver (form decided, differs from the plan above): a `Get` never sees `rangeErrSound` (`store.Get`
  reads at revision 0 and checks the minimum itself), so `readQ`/`getCall` are unchanged. Lists:
  `listCommitOk x tl R σ := if tl then lOut x σ = tooLargeL else σ.rev = uint.nat R`; `listCall … x tl Φ`
  records it in place of `σ.rev = R`; `listQ c γ γc x tl R σ`'s commit clause is
  `⌜listCommitOk x tl R σ⌝ → ∃ σ0, γc ↦□ some σ0 ∗ ⌜lOut x σ0 = lOut x σ⌝`; `Apply` sets
  `tl := decide (xs.head? = some (W64 6))` (the prophecy's error kind `ETooLarge`); new
  `lOut_tooLarge`. `call`'s list post: `∃ R, □ QL R σ ∗ ⌜y = tooLargeL ∨ R = W64 σ.rev⌝`.

## Step 3 under way (checkpoint (ii), a HARD STOP)

- Go test `examples/k8s/etcd3/errtypes_test.go` (`TestClientErrorTypes`: every schedule in a child, 6
  workers incl. deadlines/cancellations, then a closed client; fails on a `%T` outside the four).
  Log: `/shared/tmp/k8s7e1/errtypes.log`.
- Axiom attacks (subagents, scratch `/shared/tmp/k8s7e1/attack-{invoker,stream,eof}/`) on
  `grpcInvokerOk`, `cliStreamErr`, `eofOk` + `status.Error.spec` with the `clientErrTys` conjunct.
- No Lean for `clientErrTys` until 81 reviews (ii).

### Checkpoint (ii) results (2026-11-10; HARD STOP, awaiting etcd-grove-81)

- **Go test** `TestClientErrorTypes`: PASS (217s, five schedules, deadlines, cancellations, a closed client).
  Only the four types seen, each of them seen (`*status.Error`, `rpctypes.EtcdError`,
  `*errors.errorString`, `context.deadlineExceededError`). `TestReadAtRevision` (List at a past revision
  added): PASS.
- **`eofOk`, `status.Error.spec`**: not refuted (io.EOF is `errors.New`, proved in Perennial's io init;
  `status.Error(c≠OK)` is always `*internalstatus.Error`; callers pass FailedPrecondition, Unimplemented,
  Unknown). Scratch `/shared/tmp/k8s7e1/attack-eof/`.
- **`grpcInvokerOk`, `cliStreamErr`**: not refuted on etcd's configuration, but three grpc paths
  return a fifth type (`*fmt.wrapError`, or a user type with `GRPCStatus()`), each confirmed by a Go
  program against grpc v1.84.0 (`/shared/tmp/k8s7e1/attack-invoker/main_test.go`,
  `/shared/tmp/k8s7e1/attack-stream/retrycx/main.go`): (1) a per-RPC credentials error carrying a status
  (`http2_client.go:697-702`, returned raw); (2) the same wrapped with `%w`; (3) a service-config retry
  policy exhausting its attempts (`stream.go:867`, `"max retries exhausted …: %w"`). All three also break
  today's `clientErr` conjunct `isLeafError` (`*fmt.wrapError` has `Unwrap`): a bound of the existing
  trusted statements, not only of the new conjunct. etcd's configuration excludes them: `Config.DialOptions`
  empty (required by `Client__dial`/`InvClientNew`), the resolver's service config has no retry policy,
  etcd's `perRPCCredential` never errs. **Checked: `dialOptsAt` admits `.perRPCCreds pc` for any `pc` with
  `perRPCCredsOk`, whose error may be any non-nil value with a non-handler description**, so path (1)/(2)
  is open in the trust base as stated (a soundness finding on the existing `grpcInvokerOk`/`cliStreamErr`:
  their `clientErr`'s `isLeafError` can be false). Recommended: `perRPCCredsOk`'s error clause becomes
  `err = nil` (etcd's credential returns nil; its proof must then show it). Original question: whether the trusted dial/credentials
  statements (`dialOptsAt`, `perRPCCredsOk`) let a caller install credentials whose error carries a
  status or wraps one; if so, `perRPCCredsOk` should require it not to (etcd's returns nil).

## Checkpoint (ii) decided (etcd-grove-81, 2026-11-10; in `questions.md`): R1 accepted; go-ahead to (iii)

Done after the review (`50b82d8c50`, targeted build green: the bundle's proof, `Client__dial`, `InvClientNew`):
- `perRPCCredsOk`'s error clause is `err = nil` (soundness fix; finding in `notes/k8s-etcd3-plan.md`,
  "Soundness finding in the trust base"); etcd's bundle proof already had `err = nil` from
  `GetRequestMetadata.spec`. No `nonissues/` entry (etcd's credential returns nil).
- Path 3 (retry policy): nothing excluded it; `grpcResolverAt`'s docstring (axiomatized predicate,
  `InvDial.lean`) now claims "its service config sets no retry policy" (etcd's: round_robin only; no
  `GrpcDialOpt` sets a default service config). **List in the Freeze package** as a trusted-text change.
- `TestCredentialNilError` (next to `TestClientErrorTypes`); gates step 9c runs both (~4 min).

## Next, in order (the Draft's §6 steps 3-7; the next agent starts here)

0. **Merge lean** first when premise-fixes-4 has landed (it adds a no-`Format` conjunct to `statusErrOk`,
   which the `clientErr` work touches; it also changes etcdstart's premise bags and the http/fmt
   axioms). Lean at the time of writing: `f4e98c54f9` (premise-fixes-2), not merged yet.
1. **`clientErrTys`** in `Proof/go_etcd_io/etcd/client/v3/ClientErr.lean`: the four types
   (`PointerType google_golang_org.grpc.internal.status.Error.ty`, `v3rpc.rpctypes.EtcdError.ty`,
   `PointerType errors.errorString.ty`, `context.deadlineExceededError.ty`); `clientErr`'s leaf clause
   gains `ii.ty ∈ clientErrTys`. Docstrings of `grpcInvokerOk`, `cliStreamErr` name the bounds (no
   DialOptions beyond `GrpcDialOpt`'s, no retry policy, credentials returning nil).
   Producers found so far (each needs the type):
   - `clientErr_statusErrOk_of_leaf` (`ErrorsNewOk.lean:133`): add a hypothesis `e.ty ∈ clientErrTys`.
     Callers: `eofOk_of_init` (**`eofOk` is proved, not trusted**: type `*errorString` from `io`'s init),
     `ChanCtx.lean:85` (`Canceled`, `*errorString`), `ctxErrClientAllW_of` (`ErrorsNewOk.lean:220-221`).
   - For `ctxErrClientAllW_of`: do NOT strengthen `ContextErrsClient` (a closed-theorem premise, `Hcec`
     in many Results: that would be a STOP). The types come from Perennial's `context` init:
     `isPkgInit context` gives `"#HCanceledCell"` (`*errorString`) and `"#HDeadlineExceededTy"`
     (`deadlineExceededError`) (`.lake/packages/perennial/Perennial/Proof/context/Base.lean:245-249`).
   - `rpctypes_etcdError_clientErr` (`rpctypes/Error.lean:70`): `EtcdError.ty` is in the list.
   - `status.Error.spec` (axiom; `Spec/google_golang_org/grpc/status/Error.lean`): post gains the type
     (restatement, attacked, not refuted). Then `contextErrToGRPCErr`'s proof.
   - Then build the client package's leaves (`etc/importers.py --leaves --git HEAD`) and fix the rest.
   - `clientErrPlain` (`examples/k8s/etcd3/Calls.lean:65`) becomes a lemma (cases on the list,
     `go_type_set`); `Hpl` goes from the closed theorems.
2. Draft §2 (`attemptPre`'s `Ψe`, the interceptor's error outcome, `ContextError`/`waitRetryBackoff`,
   `rangeErrOut`, callers' mechanical edits). STOP if `refreshToken`'s error cannot be handled (§2.2).
3. §3.1 `Client.Get.spec` at any revision, `Client__GetAt.lean` deleted; STOP if `rangeReply_state_at`
   needs `receiptBound` (§2.4).
4. §3.2 the List prophecy patch (`etc/proph-patches/etcd/02-client-list-revision.patch`, prophcheck),
   re-translation, `Client.List` proof; STOP on owned `Kvs` if only `↦*□` is available.
5. Link/Results/Adequacy without `Hpl`/`HGetAt`/`HList`; full build; gates; tcb `--check --update` and
   collections; the Freeze package (checkpoint (iii)); stop before `land.sh`.

Trust-base changes so far for the Freeze list: `perRPCCredsOk` (narrowed), `grpcResolverAt`'s meaning
(no retry policy); to come: `clientErr`'s conjunct (so `grpcInvokerOk`, `cliStreamErr`), `status.Error.spec`.

## Step 2 (`clientErrTys`) done (eighth session, 2026-11-10)

- `clientErrTys` (`client/v3/ClientErr.lean`); `clientErr`'s leaf clause: `isLeafError ∧ AsTypeTyped ∧
  ii.ty ∈ clientErrTys`. Producers: `errorsNewOk_of`, `clientErr_statusErrOk_of_leaf` (new `hT`),
  `eofOk_of_init`, `canceledOk_of_init` (`ChanCtx`), `ctxErrClientAllW_of` (types from `context.isInit`;
  new binder `[context.Assumptions]`), `rpctypes_etcdError_clientErr`. Consumers destructuring the
  leaf clause: `ContextError`, `isSafeRetryImmutableRPC`, `leasingKV.acquire` (`⟨Hleaf, Htyped, -⟩`).
- `status.Error.spec`'s post gains the type (`*internal/status.Error`); `togRPCError` follows.
- Docstrings of `grpcInvokerOk`, `cliStreamErr` name the bounds.
- `clientErrPlain_holds` (Calls.lean); `Hpl` gone from Adequacy/Results. The driver's internal specs
  (`call`/`Apply`/`Check`/`Main*`) still take `clientErrPlain` as a premise (drop in step 6).
- Trusted statements whose meaning changes through `clientErr` (Freeze list): `grpcInvokerOk`
  (`ClientConn.Invoke`), the stream axioms through `cliStreamErr`, `waitRetryBackoff` (axiom, through
  `clientErrOk`: its error is `status.Error`'s, so true), `status.Error.spec`; plus `perRPCCredsOk`,
  `grpcResolverAt` (earlier).

## STOP before §2 (for etcd-grove-81)

- `waitRetryBackoff.spec` is an **axiom** (names-only; `etc/tcb-baseline.txt`), not a proved spec as
  the Draft's §2 said. The interceptor's error outcome needs its error's description not a handler's.
  Proposed restatement: post `clientErrOk err ∗ ⌜err = nil ∨ errDesc err ∉ handlerDescs⌝`. True of
  etcd (`retry_interceptor.go:317-374`: `contextErrToGRPCErr(ctx.Err())` is `status.Error(code,
  ctx.Err().Error())`, whose description is the context error's message; for a `ctxOk` context that is
  `"context canceled"`/`"context deadline exceeded"` (Go's contexts) or excluded by `ctxErrs`).
- `refreshToken` (§2.2): no trusted change if the interceptor's error outcome is conditional on
  `kvMethod method ∧ ∀ a ∈ addr, noRefusalAt a` (`grpcInvokerOk`'s `noRefusal` of the last attempt's
  error makes `shouldRefreshToken` false, so the refresh branch is unreachable). Cost: kubernetes
  `Client.Get`/`List` (and the store's read path) take `∀ x ∈ ms, noRefusalAt x.addr`, which the
  driver's `Main`/`MainCluster`/`MainPartition` already have (`hnr`).
- `rangeReply_state_at` (§2.4): likely no `receiptBound` (the revision-0 lemma takes the log's facts
  from `rangeReplyOk` itself, `%Hlk`; `rangeAns_st` uses the certificate instead). Not yet written.

## Step 2 review (etcd-grove-81, 2026-11-10; in `questions.md`): accepted; §2 decisions

- `waitRetryBackoff.spec` restatement approved (post `clientErrOk err ∗ ⌜err = nil ∨ errDesc err ∉
  handlerDescs⌝`), **conditional on an axiom-skill attack** (read-only subagent, scratch
  `/shared/tmp/k8s7e1/attack-wrb/`; launched by the eighth session) and a cheap Go test; refuted: STOP.
  On the Freeze list.
- `refreshToken`: the interceptor's error outcome holds under `kvMethod method ∧ ∀ a ∈ addr,
  noRefusalAt a`; `Client.Get`/`List` and the store's read path take `∀ x ∈ ms, noRefusalAt x.addr`
  (the driver's `hnr` discharges it). STOP if it reaches a closed theorem.
- §2.4 stays a STOP if `receiptBound` is needed.

## Next, in order (the next agent starts here)

0. Read the attack's result (`/shared/tmp/k8s7e1/attack-wrb/`, and the session's report); if it was
   not finished, rerun it (brief: the target, `ctxOk`'s three cases, every return path of
   `retry_interceptor.go:317-374` at the pin 673da07c8f, a Go test of `contextErrToGRPCErr`'s
   `Message()`/`%T`). Not refuted: restate `Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean`.
1. Merge lean once premise-fixes-4 has landed (raft-entsize was in land.sh at the time); full build.
2. §2 (Draft `notes/k8s-7e-1-draft.md`): `attemptPre` takes `Ψe` (`InvKVConn.lean:1278`);
   `etcdInterceptorOk` (`InvKVConn.lean:1326`) takes `Ψe` and its error side gains
   `⌜kvMethod method ∧ ∀ a ∈ addr, noRefusalAt a⌝ -∗ ⌜errDesc err ∈ handlerDescs⌝ -∗ Ψe (errDesc err)`;
   the interceptor's proof (`Client__unaryClientInterceptor.lean`: the one-attempt case ~173-195, the
   loop invariant `IHL` ~197 gains the outcome for `lastErr`, the wait error ~227 from the restated
   `waitRetryBackoff`, the refresh branch ~430 unreachable via `Hnr` and `shouldRefreshToken`'s post,
   the context-error branches from `ctxOk`/`ContextReadErrs.descs`); `ContextError`, `rangeErrOut` in
   `rangeCallOut`/`kv.Get.specM`/`client_range_any`; callers' mechanical edits.
3. §3.1, §3.2, step 6 as listed above ("Next, in order (the Draft's §6 steps 3-7)", items 3-5).

## The attack on `waitRetryBackoff` (2026-11-10): a HARD STOP (soundness finding on lean's trust base)

Result (read-only subagent; Go test `/shared/tmp/k8s7e1/attack-wrb/main_test.go`, output `out.txt`):
- **The new conjunct** `err = nil ∨ errDesc err ∉ handlerDescs`: **not refuted**. The returned error is
  always `status.Error(code, ctx.Err().Error())`, a `*status.Error` whose message is `ctx.Err().Error()`.
  For `isContext` that is "context canceled" or "context deadline exceeded" (the Cause variants too).
  For `ctxErrs`' four `clientErrTys` types it is the message, or, for a `*status.Error`, the whole
  "rpc error: code = … desc = …" string, which is never an "etcdserver: mvcc: …" description.
- **Finding:** the axiom is refuted as stated today, old post or new. `ctxOk` admits contexts whose
  `Done()` breaks Go's `context.Context` contract. `ctxQuiet` only says `Err()` returns nil; `ctxErrs`
  says "Nothing about `Done()`". Two such contexts panic in Go:
  - (a) `Done()` closed while `Err()` is nil: `contextErrToGRPCErr(nil)` calls `nil.Error()`;
  - (b) `Done()` panics (a nil receiver).
  The Go test shows both panic. Real callers meet the contract (`context.TODO`, k8s's
  `channelContext`), so this is a premise missing from `ctxOk`, not an etcd bug.
  - **Suggested fix (not applied):** `ctxQuiet` says `Done()` returns a nil channel; `ctxErrs` says
    `Done()` returns, without panicking, a channel whose close implies `ContextClosed cd.Done_gn`.
  - The same gap probably touches `grpcInvokerOk` and the other axioms that take `ctxOk`: grpc's
    `invoke` also selects on `ctx.Done()`.
- Not done: a Lean counterexample, the `notes/axiom-review` write-up, the `notes/audit.md` row.

## Decisions after the attack (etcd-grove-81, 2026-11-10; in `questions.md`)

- The `ctxOk` gap (contexts whose `Done()`/`Err()` break Go's contract) is fixed on lean's trust base by
  a separate branch, **premise-fixes-5** (with the axiom write-up and the Go counterexample). Do NOT
  change `ctxOk` here. **k8s-7e merges premise-fixes-5 when it lands** (a dependency of the Freeze).
- `waitRetryBackoff.spec` restated (done, below); on the Freeze list.
- refreshToken form and the §2.4 `receiptBound` STOP stand.

## §2 under way (ninth session, 2026-11-10)

Done (targeted build green: `client.v3.Link`, `examples.etcd.auth.SetupInv`):
- `Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean`: post `clientErrOk err ∗ ⌜err = nil ∨ errDesc
  err ∉ handlerDescs⌝` (the approved restatement of an axiom; Freeze list).
- `InvKVConn.lean`: `attemptPre … Φ (Ψe := fun _ => True)` (a default, so every old use is unchanged);
  `ifcErrOut method addr Ψe err := ⌜kvMethod method ∧ ∀ a ∈ addr, noRefusalAt a⌝ -∗ ⌜errDesc err ∈
  handlerDescs⌝ -∗ Ψe (errDesc err)` with `ifcErrOut_notin`/`_of_attempt`/`_absurd`;
  `etcdInterceptorOk`/`etcdInterceptorOkM` take a binder `Ψe` after `Φ`, ask `attemptPre … Φ Ψe`, and
  their error post gains `ifcErrOut method addr Ψe err`; `attemptPre_attempt` takes `Ψe`.
- The interceptor's proof (`Client__unaryClientInterceptor.lean`): the invoker gets `Ψe`; the loop
  invariant carries `"Heo" ∷ (⌜a = 0⌝ ∨ ifcErrOut … le)`; the wait's error by the restated
  `waitRetryBackoff`; the refresh error by `ifcErrOut_absurd` (`Hnr` and `shouldRefreshToken`'s post);
  `maxRecDepth 8192` (one `wp_if_destruct` hit the limit with the larger context).
- `EtcdInvoke.lean`: new `etcdConn.InvokeMdE.spec`/`etcdConn_InvokeMdE` (with `Ψe` and the outcome);
  `etcdConn_InvokeMd` derived from it at `Ψe := True` (its statement unchanged, so the stubs are too).

### STOP (for etcd-grove-81): the members' registrations the client sees carry no error outcome

`client_range_any`/`kv.Get.specM` reach `Range` through `kvRegsAt x` (`KVService.lean:634`), which
registers the **plain** `etcdRangeSpec`. Its metadata form `GrpcSpec.md` makes the caller give
`□ ∀ d, Ψe d`, so whatever the chain above carries, the outcome a client gets back is only what it put
in: the handler's `rangeErrReply` never reaches the client. The server proves the metadata spec with the
outcome, `isGrpcRpcMd addr Range (etcdRangeSpecM false s E γr cid mid)` (`H2` in
`etcd_kv_served`'s proof, `Results.lean:~2468`), and then weakens it to the plain registration for
`etcd_kv_served`'s conclusion, `etcdstart`'s `etcdKVAt` and `kvRegsAt`. The Draft's §0 ("server side,
done") did not see this step. Every way to carry it changes exported vocabulary or statements:
- (A, recommended) `kvRegsAt`'s Range conjunct becomes the metadata registration
  `isGrpcRpcMd x.addr Range (etcdRangeSpecM false null x.E x.γr x.cid x.mid)` (`s` is unused at
  `on = false`); `kvRegs_range` derives the plain one (`etcdRangeSpecM_false`, `isGrpcRpcMd_mono_upd`,
  `isGrpcRpc_md`), so consumers do not change. Producers: `etcd_kv_served(_with)`'s conclusion (Range in
  the metadata form, which its proof already has), `etcdstart`'s `etcdKVAt`/`etcdKVAt_regs`. A
  strengthened conclusion of an exported server theorem, and a strengthened premise (through `kvRegs`) of
  the exported results that take it (`cache/v3/Results.lean`, client `Results.lean`), each discharged by
  the server. No trust-base change.
- (B) a separate fact only on the k8s path (a new server-side export with the metadata Range registration,
  carried by `etcdstart` and the k8s Mains): more vocabulary, the same exported-statement change.
- Cost either way: `etcdRangeSpecM` asks `(⌜v3rpc.rangeCheck o ≠ none⌝ -∗ □ ∀ d, Ψe d)`, so the k8s
  reads must show `rangeCheck o = none` for their requests (sort/limit/revision checks: a pure lemma).

### (A) approved by etcd-grove-81 (2026-11-10, in `questions.md`)

Conditions: the Freeze report confirms that no closed theorem's text changes because of it and that the
trust base is unchanged; affected `interface/` files regenerated (`etc/gen-interface.py`, check which
API lists include `KVService`/`etcdstart`/`cache` modules); a pure lemma `rangeCheck o = none` for the
k8s reads (the store's Get/List requests). Not started: the ninth session stopped at its context budget
right after the decision.

### Next, in order (the next agent starts here)

1. The registration (A): `kvRegsAt` (`KVService.lean:634`), `kvRegs_range`, `etcd_kv_served(_with)`'s
   conclusion (`Results.lean` ~2430-2480: keep `H2` instead of weakening it), `etcdstart`'s `etcdKVAt`/
   `etcdKVAt_eq`/`etcdKVAt_regs` (`examples/lib/etcdstart/Served.lean`), `kvRegs_one`; then the chain above the interceptor: `kVClient.Range.spec`,
   `retryKVClient.Range.spec` (a binder `Ψe`, post `… ∗ (⌜err ≠ nil⌝ -∗ ifcErrOut
   "/etcdserverpb.KV/Range" addr Ψe err)`); `kv.Do.specG` (`doRunGen`'s range case `attemptPre … Qr
   Ψr`, `Ψr` with a default; post gains the outcome when `o.t = 1 ∧ err ≠ nil`); `kv.Get.specG`;
   `ContextError.spec`'s post gains `⌜err ≠ nil → errDesc err' = errDesc err ∨ errDesc err' ∉
   handlerDescs⌝` (38 call sites destructure its post: choose the position to break fewest; lemma
   `ifcErrOut` across it); `kv.Get.specM`/`client_range_any` gain `rangeErrOut` (Draft §2.3).
2. Draft §3.1, §3.2, step 6 as listed above. Merge lean (premise-fixes-4, then premise-fixes-5) before
   step 6.

## Steps 1-3 done, step 4 in part (tenth session, 2026-11-10; forms in `questions.md`, "tenth session")

Targeted builds green: every leaf importing `KVService`, `KVMembers`, `ContextError` and client
`Results` (`/shared/tmp/k8s7e1/leaves1.txt`, under the lock; log `a10.log`).
- **Registration (A)**: `kvRegsAt`'s Range conjunct is `isGrpcRpcMd x.addr Range (etcdRangeSpecE …)`.
  `etcdRangeSpecE` (KVService) is `etcdRangeSpecM false` without its auth parts (trivial with auth off);
  `etcdRangeSpecE_M` (KVServiceOn) and `etcdRangeSpec_E` convert. Moves: `rangeErrReply` KVServiceOn →
  KVService; `rangeFutureAt`/`rangeCompactedAt` server `ReadOn` → `InvRead` (names unchanged; this
  rebuilds the server once); KVService imports `v3rpc.Defs`. The Md conjunct also in
  `etcd_kv_served(_with)`, `etcd_kv_started(_with)`, `etcd_kv_lease_served`, etcdstart's `etcdKVAt`,
  cluster3's `memberServed_none`/`memberAt_none`, txnlin's `Check.spec`; new
  `cluster3.isGrpcRpcMd_forwards` for the Mains that build `kvRegsAt` by hand.
- **Chain**: `kVClient.Range.spec`, `retryKVClient.Range.spec` (last binder `Ψe`, post gains
  `⌜err ≠ nil⌝ -∗ ifcErrOut`), `doRunGen` (optional `Ψr`), `kv.Do.specG`, `kv.Get.specG` (last binder
  `Ψr`; post FIRST conjunct `⌜(o.t = 1 ∧) err ≠ nil ∧ sortValid o = true⌝ -∗ ifcErrOut …`).
- **`ContextError.spec`**: fourth (last) post conjunct `⌜err ≠ nil → errDesc err' = errDesc err ∨
  errDesc err' ∉ handlerDescs⌝`; all 39 call sites take `, -`; `ifcErrOut_desc` carries the outcome.
- **rangeErrOut** (step 4, client half): `rangeErrΨ`, `rangeErrOut` (KVService, persistent);
  `kv.Get.specM`'s and `client_range_any`'s post gain (last) `⌜sortValid (opGetModel key gs) = true⌝ →
  rangeErrOut ms c F (rangeWireOf …) Q err`.

Pitfalls: in this IPM `isplitr [H]` sends `H` to the RIGHT goal, bare `isplitr` sends everything right,
`isplitl [H]` sends `H` left. A spec binder left last and not determined by a hypothesis (`Ψr`) must be
passed explicitly (`(fun _ => iprop(True))`), or `unfold doRunGen` fails on the metavariable.

### Next, in order (the next agent starts here)

1. Step 4, kubernetes half: `Client.Get`/`Client.List` (and the store's read path) take
   `∀ x ∈ ms, noRefusalAt x.addr` (approved) and need `rangeCheck (rangeWireOf o) = none` for their
   requests (approved pure lemma): `rangeCheck` refuses an EMPTY key (`emptyKey`), so the k8s reads need
   `key ≠ []` (the store's keys carry its prefix) or a lemma from the store's key shape; the sort fields
   are the defaults. From `rangeErrOut`'s future half: `rangeErrReply` gives `□ Q (kvStateOf log)` and
   `rangeFutureAt o log` (`sint (len log - 1) < sint o.base.rev`), so `rangeErrSound` (R1's form) with
   `σ := kvStateOf log` (Draft §2.5, `rangeErrSound_of`).
2. §3.1 (`Client.Get.spec` at any revision, `Client__GetAt.lean` deleted). `rangeReply_state_at`:
   follow `rangeReply_state_bnd` (ClientPutGet.lean:217, takes `%Hlk` from `rangeReplyOk` itself) and
   `rangeAns_st`'s revision lemmas (KVService.lean ~1810: `hRR`, `hRle`, `kvStateOf_at_kvs`) without
   `srvLogCert_logOk`: no `receiptBound` expected (if needed: STOP).
3. §3.2, step 6 as listed above (merge lean first: premise-fixes-4, premise-fixes-5).

## Eleventh session (2026-11-10): step 4 (kubernetes half), §3.1 done; §3.2 patch done; STOP on owned `Kvs`

Decision recorded (questions.md): `Client.Get`/`List` take `key ≠ []` for the error outcome (built as a
guard in the post, see the forms in questions.md, "eleventh session").

Done (forms in questions.md):
- `Client.Get.spec` at any revision (`modAtRev`), error branch gains `(⌜key ≠ [] ∧ ∀ x ∈ ms,
  noRefusalAt x.addr⌝ → rangeErrSound opts.Revision' (fun R σ => ∃ m, Q R m σ) err)`; proof via
  `rangeReply_state_at` (no `receiptBound`: the log facts come from `rangeReplyOk`), `client_range_any`'s
  `rangeErrOut`, `rangeCheck_getKey1`, `rangeErrReply_future` (all in `kubernetes/Defs.lean`).
- `Client__GetAt.lean` deleted; `store.getList` on `Client.Get.spec`; the three revision-0 store
  callers through `Client.Get.latest` (`kubernetes/GetLatest.lean`, the old statement derived).
- `Client.List.spec`'s error branch guarded the same way (`pfx ≠ []`).
- `noRefusalAt` threaded: `getList`/`pagedChunks` (+ `kp ≠ []`), `GetList`, driver `call`/`Apply`/`Check`;
  Mains discharge it (`hnr`, `Hnr`). `HGetAt` gone from MainLinked/Results/Adequacy; links regenerated
  (`--k8s-etcd3`, `--k8setcd3`).
- List vocabulary moved down to `kubernetes/Defs.lean` (namespace `k8s` kept).
- `etc/proph-patches/etcd/02-client-list-revision.patch`; `etc/proph_patch.py --project etcd` passes;
  `etc/goose.py --project etcd` re-translated `Code/go_etcd_io/etcd/client/v3/kubernetes.lean`.

### STOP (for etcd-grove-81): an owned `Kvs` needs a trusted change

`listRespIs` asks `resp.Kvs' ↦* ps` (the store's `appendChunk` writes `kvs[i] = nil`, `store.go:1074`).
The reply reaches the client only as `Rep.recv out m'` (`grpcInvokerOk`'s success post,
`InvGrpc.lean:1323`, trusted), which `ProtoMsg.recv_persistent` makes persistent, and
`ProtoMsgT.RepSat` (trusted definition, `InvGrpc.lean:733`) yields only `T.recv l m`; the client's
`pbRangeResponseT_repSat` persists the decoded `Kvs` slice (`ownSlice_persist`, `PerTypeKV.lean:~290`).
So no proved statement can hand out the slice owned. Options in the report.

### Next, in order (after 81's decision)

1. The owned-`Kvs` route 81 picks; then the `Client.List` proof (`client_range_any` with
   `[withRangeM (prefixRangeEnd pfx), withLimitM lim, withRevM rev]`, `rangeReply_state_at`, new pure
   `srvRangeOk_page`), `Client__List: ?` out of both link files, `HList` out of MainLinked/Results/Adequacy.
2. Drop `clientErrPlain` from the driver's `call`/`Apply`/`Check`/`Main*` (step 6).
3. Merge lean (premise-fixes-4, -5 if landed), step 6 (Freeze).

## Twelfth session (2026-11-10): K1 attack (checkpoint, STOP), clientErrPlain dropped, `srvRangeOk_page`

Decisions of etcd-grove-81 recorded in `questions.md` ("after the eleventh session's STOP"): guard form and
the eleventh session's forms accepted; K1 approved on conditions (attack first); K2 rejected.

Done:
- `a2ab4bc685`: `clientErrPlain` dropped from the driver's `call`/`Apply`/`Check`/`Main*` specs; `Calls`'
  `clientErr_notTooLarge`/`unkErr_errIs`/`listErr_errIs` use `clientErrPlain_holds`; Adequacy passes
  nothing. Targeted build green (Adequacy, Results).
- `kubernetes/ListPage.lean` (new, pure): `pageOp`, `rangeWireOf_page`, `inRange_page`,
  **`srvRangeOk_page`** (the server's answer to List's range and its total count are `pageKvsL`'s);
  `prefix_not_lt` moved here from the store's `ListPages` (which imports it). Built.

**K1 attack (read-only subagent; Go test `/shared/tmp/k8s7e1/attack-kvs/`)**: NOT REFUTED in etcd's
default configuration (proto.Unmarshal resets, `Reset()` is `*x = RangeResponse{}`, repeated message
fields append to a nil slice: fresh array; retries reset; binary log copies bytes; bytes fields copied
out of the pool; no late decode; etcd's chain keeps nothing; `TestDefaultNoRace` passes under -race).
**But** with `grpc.EnableTracing = true` grpc keeps every reply (`stream.go` `LazyLog(&payload{msg: m})`)
and formats it later on `/debug/requests`: a data race with `appendChunk`'s writes (reproduced,
`TestTracingRace`, `tracing.out`). etcd sets it at log level debug (`embed/config_logging.go:234`) and in
grpc-proxy `--debug`. Bounds to name: EnableTracing false; default proto codec; no stats handler or
interceptor keeping `InPayload.Payload`; protobuf-go v2 generated reply (no custom Unmarshal). STOP for
81: how to state the EnableTracing bound (recommended: a persistent `EnableTracing ↦□ false` from grpc's
package init, required by `ClientConn.Invoke` through `isPkgInit grpc`; else a docstring bound).

### Next, in order (after 81's decision)
1. K1: `RepSat`'s post and `grpcInvokerOk`'s success post gain `Rep.recvOwn out m'`; every `RepSat` proof
   frames `True` (default); `pbRangeResponseT.recvOwn` := the owned `Kvs` cells, `rangeRespMsg` loses
   `sl ↦*□ ps`; persistent readers take it from `recvOwn` or persist it; the EnableTracing bound as decided.
2. `Client.List` proof (`client_range_any` with `[withRangeM (prefixRangeEnd pfx), withLimitM lim,
   withRevM rev]`, `rangeReply_state_at`, `srvRangeOk_page` via `rangeWireOf_page`; start = Continue or
   pfx, both with prefix `pfx`); `Client__List: ?` out of both link files; `HList` out of
   MainLinked/Results/Adequacy.
3. Merge lean (premise-fixes-4, -5), step 6 (Freeze).

### K1 attack decided (etcd-grove-81, 2026-11-10; in `questions.md`): EnableTracing bound approved

- Check done: no translated code writes `grpc.EnableTracing` (grep of `Code/`, `GeneratedProof/`,
  `TrustedCode/`, the parts: only its name declaration, `Code/google_golang_org/grpc.lean:962`; etcd's
  `embed`/logging, which set it in Go, are not translated).
- `TestDefaultNoRace` is in `examples/k8s/etcd3/kvsown_test.go` and in `etc/gates.sh` (9d, `-race`; 4s).
  **`TestTracingRace`** (the reason for the bound; not in the repo, it needs `golang.org/x/net/trace`):
  `/shared/tmp/k8s7e1/attack-kvs/kvs_test.go`, output `tracing.out`: with `grpc.EnableTracing = true`,
  grpc's client trace keeps every reply (`stream.go` `csAttempt.recvMsg`:
  `LazyLog(&payload{sent: false, msg: m})`) and formats it lazily (`trace.go:125-130`) when
  `/debug/requests` is rendered: a race with the caller's `resp.Kvs[j] = nil`. etcd sets the flag in
  `embed.Config.SetupGlobalLoggers` at log level debug and in grpc-proxy `--debug`.

### STOP (twelfth session, for etcd-grove-81): where the EnableTracing cell comes from

grpc is translated names-only: its `initialize'` runs no `GlobalAlloc` (only the `X.init` axioms of the
variables with initializers and the `init.<k>`s), and `EnableTracing` (`var EnableTracing bool`, no
initializer) has no `X.init`, so no step of grpc's init allocates its cell. A ghost-only axiom
(`⊢ |==> globalAddr EnableTracing ↦□ false`) is unsound in this model: `wp_alloc` may return
`globalAddr EnableTracing` for an ordinary `new` while the cell is unallocated (`wp_GlobalAlloc`'s
angelic check shows global addresses are ordinary fresh locations), giving two points-tos. So the fact
must be the post of a step of grpc's init. Options:
- (a) recommended: a trust-boundary axiom of `grpc/Init.lean` (generated: a `SPECIAL['google_golang_org.grpc']`
  entry in `etc/gen-init.py`) on grpc's FIRST untranslated variable initializer (`DefaultBackoffConfig.init`,
  taken out of `opaqueInitsOk`), post `globalAddr EnableTracing ↦ false`, docstring: Go allocates every
  package variable, zero-valued, before the first initializer runs (`var EnableTracing bool`, `trace.go:33`
  at v1.84.0), and grpc's names-only translation has no `GlobalAlloc` for it, so the allocation is
  attributed to the first step of the package's initialization; persisted in `finish`; grpc's fact
  (`cache/v3/Base.lean`'s `grpc_is_pkg_init_inst`, now `True`) becomes `grpcInit := globalAddr
  EnableTracing ↦□ false`; a program that writes it needs the cell exclusively, which no one has.
- (b) a translator-side fix (goose emitting `GlobalAlloc` for names-only variables): a Perennial change,
  general, but not for this stage.

### K1 implementation plan (the next agent; after 81 decides the cell's source)

Trusted (Freeze list): `InvGrpc.lean` `ProtoMsgT.RepSat`'s post `T.send ls m ∗ T.recv l m ∗ T.recvOwn l m`;
`grpcInvokerOk`'s success post `∃ m', Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m'`; docstring of both
names the bounds (EnableTracing false from grpc's init; grpc's default proto codec; no stats handler or
interceptor keeping the reply; reply types protobuf-go v2 generated code; `TestDefaultNoRace`).
Decide whether `StreamMsgT.RepSat` (`InvGrpcStream.lean:156`) follows (not needed for k8s: leave it).
`pbRangeResponse` (`PerTypeKV.lean`): `recvOwn l m := ∃ sl ps, Kvs field ↦□ sl ∗ sl ↦* ps` (or keyed on
the same `sl`/`ps` as `recv`: better make `rangeRespMsg` existentially fix `sl`, `ps` and let `recvOwn`
say `sl ↦* ps` for THOSE: e.g. `recvOwn l m := ∃ sl ps, structFieldRef … Kvs l ↦□ sl ∗ sl ↦* ps ∗
txn.kvsIs ps m.kvs`, and drop `sl ↦*□ ps` from `rangeRespMsg`; consumers combine the two `Kvs ↦□` to
equate `sl`). Then:
1. 17 `*_repSat` proofs (PerTypeKV/KVRest/Lease/Auth, PerTypeWatch, PerTypeLeaseKeepAlive): frame the
   default `True`; `pbRangeResponseT_repSat` keeps `Hsl` owned (no `ownSlice_persist`).
2. Chain statements with `Rep.recv out m' ∗ Φ m'` gain `Rep.recvOwn out m'`: `EtcdInvoke.lean:69,94,117`
   (`etcdInterceptorOk*`), `InvKVConn.lean:1395,1440`; their proofs move it along.
3. `kVClient.Range`/`retryKVClient.Range`/`kv.Do`/`kv.Get` (`Spec/.../kv__Get.lean`), `rangeCallOut`,
   `client_range_any`, client `Results.lean:2662,2935,2989` (EXPORTED statements: list in the Freeze
   report) gain the owned cells next to `rangeRespMsg`.
4. Consumers that load `Kvs` (26 files mention `rangeRespMsg`: `grep -rln rangeRespMsg Proof Spec`):
   persist the cells where they read them (`ownSlice_persist`), or keep them owned (`Client.List`).
5. Then `Client.List`'s proof (plan above, `srvRangeOk_page`), `HList` out.

Size: about 40 files; a full day's work with targeted builds. Budget it before starting.

## Thirteenth session (2026-11-10): EnableTracing cell (a), K1 trusted edits and the client chain

Decision recorded (`questions.md`, "EnableTracing cell source"): option (a), approved by etcd-grove-81.

Done (commits on `k8s-7e`):
- `425d7ed79c`: `etc/gen-init.py` `SPECIAL['google_golang_org.grpc']`: grpc's first initializer's axiom
  `DefaultBackoffConfig_init` (`{{True}} DefaultBackoffConfig.init #() {{RET #(); globalAddr EnableTracing ↦ false}}`;
  out of `opaqueInitsOk`, whose post was `True`: nothing else changes meaning), persisted in `finish`;
  `cache/v3/Base.lean`: `grpcInit := globalAddr google_golang_org.grpc.EnableTracing ↦□ false`, grpc's fact
  (was `True`). `etc/gen-init.py --check` clean. Rebuilds ~6300 modules (cache `Base`).
- `1eb0c1b286` (TRUSTED, Freeze list): `InvGrpc.lean` `ProtoMsgT.RepSat`'s store post `send ∗ recv ∗ recvOwn`;
  `grpcInvokerOk`'s success post `∃ m', Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m'`; docstrings name the
  bounds (EnableTracing false through `isPkgInit grpc` of `ClientConn.Invoke`; default proto codec; no stats
  handler (no `GrpcDialOpt` for one) or interceptor keeping the reply; protobuf-go v2 generated reply types;
  `TestDefaultNoRace`). `StreamMsgT.RepSat` left alone. New `ProtoMsgT.repSat_of_recvOwn_true` (the 14 default
  `*_repSat` proofs: one `apply` line each; Watch/LeaseKeepAlive are `StreamMsgT`, untouched).
  `InvKVConn.lean`: `rangeRespRecv` (header, More, Count), `rangeRespKvsOwn` (`Kvs ↦□ sl ∗ sl ↦* ps ∗
  txn.kvsIs ps m.kvs`; the name `rangeRespOwn` is taken by cache/v3), `rangeRespMsgO := recv ∗ own`,
  `rangeRespMsgO_persist` (⊢ |==> rangeRespMsg); `pbRangeResponse.recv := rangeRespRecv`, `recvOwn :=
  rangeRespKvsOwn`, `send` stays `rangeRespMsg`; `rangeCallOut`'s success on `rangeRespMsgO`;
  `etcdInterceptorOk(M)` and `EtcdInvoke`'s three statements carry `Rep.recvOwn`. `pbRangeResponseT_repSat` keeps
  the slice owned. The interceptor's proof needed no change.
- `23b2325664`: the 15 stub proofs (`etcdserverpb/*Client__*`) take `recvOwn` (`-` or `Ho`); `rangeCallOutP` (the
  old persistent form) and `rangeCallOut_persist`; `rangeCallOut_st` takes `rangeCallOutP`, so `kv.Get.spec`
  is UNCHANGED (its proof persists); **`client_range_any`'s post is `rangeRespMsgO`** (EXPORTED statement:
  Freeze list); its readers persist (`client_range_end_to_end`, `client_get_on` (ResultsOn), `ClientPutGet`,
  txnlin `Calls`) with `iapply wp_fupd` before the call and `imod rangeRespMsgO_persist`/`rangeCallOut_persist`.
  So far the only exported statement change of K1 besides the trusted ones; the plan's other Results
  (2935/2989/3161) keep `rangeRespMsg`.

Then (same session):
- `19390bf319`: `ServerKVGet` and kubernetes `Client.Get` persist the owned reply. **Full build green** after
  K1 (13795 jobs, `/shared/tmp/k8s7e1/full2.log`). `etc/tcb-report.py --check` (before `Client.List`): the
  only difference from the baseline is NEW `axiom Perennial.google_golang_org.grpc.DefaultBackoffConfig_init`
  (expected; baseline not yet updated).
- `91d9a21fcf`: **`kubernetes.Client.List` proved** (`Proof/go_etcd_io/etcd/client/v3/kubernetes/Client__List.lean`,
  no sorry; local lemmas `rangeCheck_page`, `sepL2_of_kvsIs`; the `if Continue != ""` branch handled by
  `generalize hstart` + `all_goals`); linked: `etc/link-lean-first-k8s.txt` gains `WithRange`, `getPrefix`,
  `GetPrefixRangeEnd`, `Client__List: WithRev WithLimit WithRange GetPrefixRangeEnd`; `Client__List: @` in
  `k8s-etcd3`/`k8setcd3`; the three Links regenerated (`--k8s`, `--k8s-etcd3`, `--k8setcd3`). `HList` gone
  from MainLinked/Results/Adequacy: `git diff lean` of `Adequacy.lean` is empty, of `MainLinked.lean` only
  `wp_noStreaming` (7e-4's), of `Results.lean` only the header prose. Targeted build green (the three
  Links, MainLinked, Results, Adequacy).

Next, in order (the next agent starts here):
1. Merge lean (at `ef6bc4663b`: premise-fixes-2, premise-fixes-3, raft-entsize; premise-fixes-4/-5 not
   landed yet as of this session): conflicts expected in notes (one copy of each Last-updated entry,
   status-history append only), tcb files (take lean's, re-update after the build), maybe
   `etc/gen-init.py` (raft-entsize's rafthttp SPECIAL; keep both, then `etc/gen-init.py --check`).
2. Full build; `etc/tcb-report.py --check --update` and the collections (`--collection ... --check --update`
   for those that move); expected tcb diff vs lean: + `DefaultBackoffConfig_init`, plus what 7e-2/7e-4 add
   (their accepted Freeze packages); `opaqueInitsOk` (grpc) loses `DefaultBackoffConfig.init` from its list.
3. Step 6 (Draft §6), then checkpoint (iii), the Freeze package: full `etc/gates.sh`; regenerate interfaces
   (`etc/gen-interface.py`, client and grpc API changes: `RepSat`, `grpcInvokerOk`, `client_range_any`,
   `pbRangeResponse`); the report lists the trusted-text changes (grpc Init `DefaultBackoffConfig_init` +
   `grpcInit`; `RepSat`; `grpcInvokerOk`), the exported statement changes (`client_range_any`'s post
   `rangeRespMsgO`; `etcdInterceptorOk(M)`/EtcdInvoke posts carry `Rep.recvOwn`), and that no closed
   theorem's text changes beyond losing Hpl/HGetAt/HList.

## Fourteenth session (2026-11-10): lean merged, full build, tcb, Freeze package

- `a645781811`: lean `ef6bc4663b` (premise-fixes-2, premise-fixes-3, raft-entsize) merged, **no
  conflicts**; `etc/gen-init.py --check` clean.
- Full build green, **13811 jobs** (`/shared/tmp/k8s7e1/full3.log`).
- `etc/tcb-report.py --check`: the only difference was NEW `grpc.DefaultBackoffConfig_init` (approved);
  `--check --update`; 13 collections took the same one line (cachekv, compactkv, k8scompactor,
  k8setcd3, leasecatchup, leaseexpiry, leasekv, linkv3p, linkvtxn, m2, putget, putget3, watchkv).
  Interfaces regenerated: only `etcdstart/Served.txt` changed. Commit `a8360265f4`.
- **The Freeze package: `notes/k8s-7e-freeze.md`** (closed theorems' statements = lean's, checked
  also on the 43728 constants reachable from their types; trusted-text changes; tcb +22/−0; exported
  statements; bounds allow-list; gates).
- STATUS "Last updated": k8s 7e entry added, the oldest (mvcc API merge) moved to status-history.
- Gates: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G env
  TMPDIR=/shared/tmp LAKE_PACKAGES=/shared/tmp/manifest-ddc.json
  PERENNIAL_CHECKOUT=/shared/perennial-ddc0f0acc timeout 14000 bash etc/gates.sh`
  → `/shared/tmp/k8s7e1/gates1.log` (result below).

Next: etcd-grove-81's review of the Freeze package; when lean moves (premise-fixes-4, -5), merge it
again (pf4: rnSetLoggerOk out of the premise bags, no-Format facts in statusErrOk/errStrOk/context
errors/http-fmt axioms; pf5: ctxDone in ctxErrs/ctxQuiet, keySized dropped; expect conflicts in
ClientErr/InvGrpc/context predicates and the tcb files), full build, tcb `--check --update`, gates
again; then land.sh only on 81's go.
