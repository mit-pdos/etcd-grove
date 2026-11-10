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
