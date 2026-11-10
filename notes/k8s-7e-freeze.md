# k8s 7e: the Freeze package (7e-1 with 7e-4, 7e-2, 7e-3b), 2026-11-10

Branch `k8s-7e` (worktree `/shared/etcd-grove-k8s7d`), against lean `ef6bc4663b` (premise-fixes-2,
premise-fixes-3, raft-entsize), merged at `a645781811` (no conflicts). The 7e-4 Freeze package
(`notes/k8s-7e-4-handoff.md`, "Steps 5 and 6") was accepted by etcd-grove-81; 7e-2's trusted texts
were reviewed and accepted (`notes/k8s-7e-2-handoff.md`, "Eighth session"); 7e-1's trusted
restatements were each approved before they were built (`questions.md`, "k8s 7e-1 ..."). This file
puts the whole branch's delta against lean in one place.

## 1. The closed theorems carry exactly lean's premises

`k8s_etcd3_safe`, `k8s_etcd3_cluster_safe`, `k8s_etcd3_partition_safe` (`Results.lean`) and
`k8s_etcd3_adequate`, `k8s_etcd3_cluster_adequate`, `k8s_etcd3_partition_adequate` (`Adequacy.lean`):

- `git diff lean -- .../examples/k8s/etcd3/Adequacy.lean`: **empty**.
- `git diff lean -- .../examples/k8s/etcd3/Results.lean`: **header prose only** (the list of
  `Apply`'s operations gains `GetList`; a paragraph "No pending hypotheses (k8s 7e-1)"). No theorem
  statement changes: the pending hypotheses `Hpl`, `HGetAt`, `HList` of the 7e-4 state are gone, and
  the six statements are lean's, character for character.
- `MainLinked.lean`: two proof terms gain `wp_noStreaming` (7e-4's linked callee); no statement change.
- **The definitions the statements are written in.** A Lean script
  (`/shared/tmp/k8s7e1/reach/Reach.lean`) collected every constant reachable from the six theorems'
  types (through definitions' bodies and types, not proofs): 43728 constants. Those whose module's
  source file differs from lean's (`/shared/tmp/k8s7e1/reach/hit.txt`):
  - the translated program, as expected: `Code.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3`
    (489: the driver with `GetList`, 7e-3b/7e-4), `Code.go_etcd_io.etcd.client.v3.kubernetes` (128:
    the List prophecy patch, 7e-1), `Code.github_com.spf13.pflag` (343, names only, 7e-4),
    `Code.k8s_io.component_base.featuregate` (69, re-translated with its interfaces, 7e-4),
    `Code.k8s_io.apimachinery.pkg.{fields,labels}` (86 + 95, `Set.Get`/`Set.Has` translated, 7e-2);
  - 11 constants of three `Proof` modules (`cluster3.{premises,BootFacts,bootPremise,dir3,initURLs3,
    urlsOk}`, `cache/v3/Base`'s `zap`/`zapcore`/`metadata` package-init instances, `InvGrpc`'s
    `grpcRunCtx`/`etcdPkgPrefix`): each one's text is **identical** to lean's
    (`/shared/tmp/k8s7e1/reach/cmpdefs.py`). No `Spec` module is reached.
  So the premises (`k8s_etcd3.premises` → `etcdstart.premises`, `ContextReadErrs`, the `BootFacts`,
  `ckptEffectsOk`, `authRecordsFit`, `grpcRepliesFit`, ...) mean what they mean on lean; only the
  program they are about changed.

## 2. Trusted-text changes on k8s-7e against lean

Mechanical source: `python3 /shared/tmp/premise-fixes-4/axdiff.py` (axioms, opaques and defs
changed, `/shared/tmp/k8s7e1/axdiff.txt`) plus every changed `Spec` file whose `Proof` file is an
axiom. `TrustedCode/`: no change.

### 2.1 Axioms added (22, all in the TCB baseline below)

7e-2 (reviewed and accepted, attacked T1-T15, Go tests in `examples/k8s7e2attack`):
- `reflect.{Append, Copy, KindCompare, MakeSlice}.wp_proof`, `reflect.Type.Elem.wp_proof`,
  `reflect.Value.{Cap, IsNil, Kind, Len}.wp_proof` (new specs, `Spec/reflect/`);
  `reflectM.type_intoVal_inj` (`go.IntoValInj reflect.Type'`, the `heapTypedPointsto` pattern) and
  `reflectM.type_into_val_typed` (`Proof/reflect/Values.lean`; plus the opaque `reflSliceV`);
- `apimeta.GetItemsPtr.wp_proof`, `metrics.RecordListLatency.wp_proof`,
  `metrics.RecordStorageListMetrics.wp_proof`, `apierrors.IsTimeout.wp_proof`,
  `encoding.json.Marshal.wp_proof` (with the opaques `tokJson`, `function` in `json/Token.lean`);
- `apierrors.HasStatusCause.wp_proof` (was a named hypothesis `?` of the DaemonSet track on lean;
  now an axiom with precondition `apiErrOk err`, after the typed-nil refutation);
- `encoding.base64.RawURLEncoding_init` (opaque `rawUrlEnc`; `RawURLEncoding.init` leaves
  base64's `opaqueInitsOk`);
- `k8sfeature.featureOff_persistent` (sweep repairs 1's B5, existing text, first linked here).

7e-4 (accepted): `github_com.spf13.pflag.opaqueInitsOk` (pflag names only, `etc/gen-init.py`);
`k8s_io.apimachinery.pkg.util.version.opaqueInitsOk` (already on lean, now reached).

7e-1 (approved by etcd-grove-81, "EnableTracing cell source"): `google_golang_org.grpc.
DefaultBackoffConfig_init`, `{{True}} DefaultBackoffConfig.init #() {{RET #(); globalAddr
EnableTracing ↦ false}}` (`etc/gen-init.py` `SPECIAL['google_golang_org.grpc']`); grpc's
`opaqueInitsOk` loses `DefaultBackoffConfig.init` from its list, nothing else; grpc's package fact
`grpcInit` (`cache/v3/Base.lean`) is `globalAddr EnableTracing ↦□ false` (was `True`).

The `Code/` axioms the translator adds for pflag's types (`Code/github_com/spf13/pflag.lean`, 196
type axioms) and the 9 removed from featuregate (`FeatureSpec`, `MutableFeatureGate`,
`MutableVersionedFeatureGate`, now translated interface types) are generated names, not in the TCB.

### 2.2 Axioms removed

None (no axiom or `sorry` leaves the baseline).

### 2.3 Axioms restated (statement changed)

7e-1 (each approved; attacks and Go tests before building):
- `status.Error.wp_proof` (`Spec/google_golang_org/grpc/status/Error.lean`): post gains
  `∀ ii, err = ok ii → ii.ty = *internal/status.Error` (first of `clientErrTys`).
- `waitRetryBackoff.wp_proof`: post gains `err = nil ∨ errDesc err ∉ handlerDescs` (attacked; not
  refuted; the ctxOk gap it found went to premise-fixes-5).
- Through trusted definitions (below): every axiom whose post says `clientErrOk`/`clientErr`
  (`grpcInvokerOk`, `cliStreamErr`, `eofOk`, ...) now also says the error's dynamic type is in
  `clientErrTys` (`TestClientErrorTypes`, gates 9c); every axiom stated with `grpcInvokerOk` or
  `RepSat` carries `Rep.recvOwn` (`TestDefaultNoRace`, -race, gates 9d).

7e-2 (accepted):
- `apierrors.HasStatusCause.wp_proof` (above); `metrics.RecordDecodeError.wp_proof`,
  `metrics.RecordEtcdRequest.wp_proof`: premises `utf8Valid` of their labels (R1, trust-base repair,
  `nonissues/k8s-apiserver-metrics-negative-or-non-utf8-panic.md`; RecordEtcdRequest also keeps
  premise-fixes-3's `statusErrOk err`);
- `tracing.Start.wp_proof`: post gains `□ (ctxNeverDone ci -∗ ctxNeverDone ci')` (B2;
  `TestTracingStartDoneNil(SDK)`);
- `reflect.ValueOf.wp_proof`: also `Elem()` of a non-nil pointer (`reflElem`); `reflect.Value.Set.
  wp_proof`: also a slice `Value` (`reflSliceV`), post `p ↦ y`;
- `encoding.base64.StdEncoding_init`: post `stdEncInit` (was `base64Init`, now
  `stdEncInit ∗ rawUrlEncInit`; same content for StdEncoding); opaque `stdEnc` docstring only;
- `rpctypes.ErrCompacted_init`, `ErrFutureRev_init`: post gains "an `EtcdError` value"
  (`TestRpctypesErrTypes`); `rpctypesInit` (cache/v3 `Base`) carries it.

### 2.4 Trusted definitions changed (vocabulary of axioms)

- `InvGrpc.lean` (7e-1, approved): `ProtoMsgT.RepSat`'s store post `send ∗ recv ∗ recvOwn`;
  `grpcInvokerOk`'s success post `∃ m', Rep.recv out m' ∗ Rep.recvOwn out m' ∗ Φ m'` (docstring bounds:
  `EnableTracing` false through `isPkgInit grpc`, default proto codec, no stats handler/interceptor
  keeping the reply, protobuf-go v2 reply types); `perRPCCredsOk`: `GetRequestMetadata` returns no
  error (was: an error whose description is not a handler's; soundness fix, decided by
  etcd-grove-81).
- `ClientErr.lean` (7e-1, approved): new `clientErrTys` (the four types); `clientErr`'s leaf clause
  gains `ii.ty ∈ clientErrTys`.
- `InvKVConn.lean` (7e-1): `pbRangeResponse.recv := rangeRespRecv`, `recvOwn := rangeRespKvsOwn`
  (the default replies keep `recvOwn = True`, `ProtoMsgT.repSat_of_recvOwn_true`); `etcdInterceptorOk(M)`
  take `Ψe`, error post `ifcErrOut`, success post `Rep.recvOwn`; `attemptPre` gains `Ψe`.
- `cache/v3/Base.lean`: `grpcInit` (above), `rpctypesInit` (above); `encoding/base64/Base.lean`:
  `base64Init` = `stdEncInit ∗ rawUrlEncInit`.
- `k8s_io/apiserver/pkg/storage/etcd3`: `Contract.transformerOk`, `Store.{isStore, respIs, unkErr}`,
  `Updates.{KvNext, k8sAu1, k8sAuRW}` (7e-2's list path; specs' vocabulary, not under an axiom).

### 2.5 Init axioms (generated, `etc/gen-init.py --check` clean)

grpc: `DefaultBackoffConfig_init` new, `opaqueInitsOk` list −1; base64: `RawURLEncoding_init` new,
`StdEncoding_init` restated, `opaqueInitsOk` list −1; rpctypes: `ErrCompacted_init`/`ErrFutureRev_init`
restated; pflag: `opaqueInitsOk` new; the driver's `errNoList` initializer gone (`_K8E`).

### 2.6 Other trusted inputs

- Prophecy patch `etc/proph-patches/etcd/02-client-list-revision.patch` (`NewProph`, `ResolveU64`
  of `resp.Revision` before `List`'s success return); `etc/prophcheck` passes (goose `--check`).
- Goose configurations: `pflag.toml` (names only, new), `featuregate.toml` (imports context, pflag,
  version), `fields.toml`/`labels.toml` (`Set.Get`, `Set.Has` translated: proved, not trusted).

## 3. TCB diff against lean

`etc/tcb-baseline.txt`: **+22 axioms (exactly §2.1's), −0, sorries unchanged** (848 → 870
entries; `git diff lean -- etc/tcb-baseline.txt`). Against the 7e-4 package's baseline the only new
entry is `DefaultBackoffConfig_init` (`etc/tcb-report.py --check` after the merge's build).

Collections (`git diff lean --stat -- etc/tcb-collections`), additions only:
k8setcd3 +22, k8s +16 (7e-2's), k8scompactor +4 (pflag, version, `RawURLEncoding_init`,
`DefaultBackoffConfig_init`), and +2 (`RawURLEncoding_init`, `DefaultBackoffConfig_init`) in each of
cachekv, compactkv, leasecatchup, leaseexpiry, leasekv, linkv3p, linkvtxn, m2, putget, putget3,
watchkv. The other 38 collections unchanged.

## 4. Changed exported statements

Results files (`git diff lean -- '*Results*.lean'`):
- `client/v3/Results.lean`: `client_range_any`'s post: success on `rangeRespMsgO` (owned `Kvs`;
  `rangeRespMsgO_persist` gives lean's `rangeRespMsg`), and a new conjunct
  `sortValid … = true → rangeErrOut ms c F (rangeWireOf …) Q err`. `etcd_kv_served(_with)`,
  `etcd_kv_started(_with)`, `etcd_kv_lease_served`: the `Range` registration is
  `isGrpcRpcMd addr Range (etcdRangeSpecE …)` (stronger conclusion; approved option (A)).
- `client/v3/ResultsOn.lean`: the same registration form; new lemma `isGrpcRpcMd_forwards`.
- `examples/k8s/etcd3/{Results,MainLinked}.lean`: no statement change (§1).

Interfaces: only `interface/.../etcdstart/Served.txt` changed (`etcdKVAt`'s Range registration
form, as above); backend, bbolt, mvcc, raft unchanged.

Linked specs changed (`git diff lean --name-status -- Spec/`: 74 added, 47 modified):
- trusted (§2.3): `status.Error`, `waitRetryBackoff`, `HasStatusCause`, `RecordDecodeError`,
  `RecordEtcdRequest`, `tracing.Start`, `reflect.ValueOf`, `reflect.Value.Set`;
- proved, client chain (7e-1): `kVClient.Range` and `retryKVClient.Range` (binder `Ψe`, post
  `ifcErrOut`), `ContextError` (fourth conjunct on the description), `kubernetes.Client.Get` (at any
  revision; error guard `rangeErrSound`; `GetAt` deleted), `kubernetes.Client.List` (new, proved);
  txnlin `Check.spec` (Md registration premise);
- proved, store (7e-2): `etcd3.New`, `store.getCurrentState`, `store.validateMinimumResourceVersion`,
  the two list-error aggregator factories, `storage.NewInternalError`,
  `storage.NewTooLargeResourceVersionError`, `apierrors.NewResourceExpired`, and the new list path
  (`GetList`, `getList`, `pagedChunks`, ...);
- the driver (7e-3b/7e-4): every `examples/k8s/etcd3` spec over the new model (`Model`, `step`,
  `Apply`, `call`, `Check`, codecs, versioner, `seed`, `workloadKeys`, ...); `Main*` specs: docstring
  and imports only.

## 5. Bounds allow-list

`etc/bounds-allow.txt` (decided by etcd-grove-81; follow-up: `threadTok` through the store's
`isStore`):
- `spec-thread ^Spec/k8s_io/apiserver/pkg/storage/etcd3/(New|store__GetList|store__getList|store__pagedChunks)\.lean$`
  (7e-2: `collectorMux`'s `RWMutex` reader-slot bound `threadBound GF ≤ 2^30-1`);
- `spec-thread ^Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/(call|Apply|Check)\.lean$`
  (7e-4: the driver passes it on).

## 6. Gates

Against lean `ef6bc4663b` (`/shared/tmp/k8s7e1/gates1.log`): build (13811 jobs), links, tcb (865
axioms, 5 sorries), collections (53 match), goose (40), gen-init (224) passed; the run was stopped
before model-param-check when lean moved (premise-fixes-4, then the mvccfull sync). To redo after the
sync merge (`notes/k8s-7e-1-handoff.md`, "Merge order").

## 7. After the premise-fixes-4 merge (`65c1217456`, not yet built)

One trusted text combines two approved changes: `rpctypes.ErrFutureRev_init`/`ErrCompacted_init`
(and `rpctypesInit`) carry both pf4's `methodSet e.ty !! "Format" = none` and 7e-2's "an `EtcdError`
value". The internal lemma `clientErr_statusErrOk_of_leaf` takes both `hT` and `hF`.
