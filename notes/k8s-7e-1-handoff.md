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
