# Translating the Kubernetes etcd3 store with Goose (survey, 2026-10-22)

Goal: find what Goose/Perennial support is missing for verifying the Kubernetes API server's
etcd3 storage backend (`k8s.io/apiserver/pkg/storage/etcd3`, the store `TestCorrectness` runs
against; `test/integration/apiserver/storage/` in kubernetes). Perennial and the pinned translator
are unchanged; the gaps below are worked around in this repository's Goose configuration, and the
general fixes are for independent Perennial branches.

## Setup

- `examples/k8setcd3`: a Go module requiring `k8s.io/apiserver` at master
  (`v0.0.0-20261021221356-9c4ec15b8038`, published from kubernetes master of 2026-10-21) and
  replacing etcd's modules by the etcd fork at the etcd project's pin (`2aed163b1`, pseudo-versions
  `v3.0.0-20261020174036-2aed163b15c6`). k8s pins etcd client v3.7.2; **it builds against the
  fork unchanged** (`GetStream`, `RangeStreamResponse`, `WithWatchBufLog`, `client/v3/kubernetes`
  all exist there).
- `etc/goose.py` project `k8s-apiserver` (local, examples/k8setcd3): with bodies
  `storage/etcd3` and `storage` (preconditions, continue tokens, errors, `SelectionPredicate`,
  `APIObjectVersioner`); types and names only (their `.toml`) the 30 packages they name: 17 of
  apimachinery, 8 of apiserver, component-base's `tracing`/`featuregate`, klog, `k8s.io/utils/clock`,
  and the standard library's `encoding/json`, `encoding/base64`, `iter`, `path` (Perennial
  translates none of them). It owns `Code/k8s_io/{apiserver,apimachinery,klog,component_base,
  utils/clock}`, so the etcd project now owns `k8s_io/utils/third_party` (the btree) instead of
  all of `k8s_io`.
- The etcd project also translates `go.etcd.io/etcd/client/v3/kubernetes` with bodies (the
  client the store calls: `Get`, `List`, `Count`, `OptimisticPut`, `OptimisticDelete`) and grpc's
  `grpclog` names only.
- Result: `etc/goose.py --check` passes for both projects; `Code.*` and `GeneratedProof.*` of
  `storage/etcd3`, `storage`, `client/v3/kubernetes` and all the names-only packages build (653
  jobs; `Code.k8s_io.apiserver.pkg.storage.etcd3` 44 s). No type of the three body packages is
  axiomatized.

## Gaps

**G1. Field selection through a type alias of a struct** (Goose rejects: `[impossible(go)]:
expected (pointer to) struct type for base of selector, got *clientv3.Event`).
`clientv3.Event` is `type Event = mvccpb.Event`; `getStructInfo` (`goose/types.go:358`) matches
`*types.Named` without `types.Unalias`. Hits `compact.go:308` (`compactor.fromWatchResponse`,
`lastEvent.Kv`), `event.go:80` (`parseEvent`, `e.Kv`), `watcher.go:516`
(`watchChan.startWatching`, `e.Type`). Workaround here: the three are names only
(`etcd3.toml`). General fix: `types.Unalias` on the type and on a pointer's element in
`getStructInfo`; tried in a scratch copy of the pinned translator: with it the three functions
translate, and their `Code` and `GeneratedProof` elaborate (nothing else changes). Needed for the
watcher (every event goes through `parseEvent`) and the compactor.

**G2. Range over a function** (Goose: `[unsupported]: range over func(yield func(listChunk,
error) bool) (only integers, maps, slices, channels and arrays are supported)`), `store.go:825` in
`store.GetList`: `for chunk, chunkErr := range chunks`, where `chunks` is an
`iter.Seq2[listChunk, error]` from `pagedChunks` (`store.go:881`, the ordinary paged path) or
`streamChunks` (`store.go:937`, the `EtcdRangeStream` path). So turning the feature gate off does
not avoid it: **every `GetList` goes through it**. Workaround here: `store.GetList` names only.
Options: (a) Goose support for range-over-func (desugar the loop into a call of the iterator with
a closure whose `break`/`continue`/`return` set flags; the iterator functions themselves,
closures calling `yield`, already translate); (b) a fork of k8s.io/apiserver for Goose (as the
etcd fork) rewriting the loop as an explicit `pagedChunks` loop; (c) `GetList` trusted with a
model. (a) is the general change; it is the main blocker for the list path.

**G3. A type of a package the file does not import** (Lean: `Unknown identifier`). When a body
uses a method or value whose type belongs to a package the Go file does not import, Goose adds no
import for it, and `pkgRef` (`goose/goose.go:2967`) refers to it through an imported package of
the same name if there is one:
- `utilfeature.DefaultFeatureGate.Enabled(...)` names `featuregate.FeatureGate`
  (k8s.io/component-base/featuregate), not imported by etcd3 or storage: nine functions of etcd3
  (`New`, `NewCompactor`, `store.Delete`, `shouldStream`, the watcher's feature checks) and
  `SelectionPredicate.ShardingEnabled`. Workaround here: `util/feature.toml` imports
  `featuregate` (names only), so the name reaches importers through the public import (the
  `zap` → `zapcore` trick); all ten translate and elaborate.
- `storage.InvalidError.Error` calls `field.ErrorList.ToAggregate().Error()`: the `Aggregate`
  interface of `k8s.io/apimachinery/pkg/util/errors` is emitted as `_root_.Perennial.errors.Aggregate`
  (the standard library's `errors`, imported under the same name): wrong, not only missing.
  Workaround: names only (`storage.toml`).
General fix: import the Lean module of every package whose types a translated body names, and
never substitute a same-named package in `pkgRef` (error instead).

**G4. Interfaces and structs of names-only packages are axiomatized** unless the package's
config imports what their definitions name (`translate_types` skips such a type). For the store
this matters: `runtime.Object`, `runtime.Encoder`/`Decoder`/`Codec` (the codec the store encodes
and decodes with), `metav1.Object` (what `meta.Accessor` returns; the versioner reads and sets
resource versions through it), `ObjectMeta`, `ListMeta`. Done here: `runtime.toml` imports
`schema` and `io`, `meta/v1.toml` imports `types`, `runtime`, `schema` and `time`: all of these are
now concrete (only `metav1.InternalEvent` stays axiomatized). `value.Transformer` was concrete
already. Not a Goose gap, configuration.

## What the proofs will need beyond the translation (not missing support, but work)

- **`reflect` on every unary path.** `Delete`/`GuaranteedUpdate` take `v := conversion.EnforcePtr(out)`
  and allocate with `reflect.New(v.Type()).Interface().(runtime.Object)`
  (`stateFromEtcdResponse`, `store.go:1190`); lists build the result with `reflect.MakeSlice`,
  `reflect.Append`, `reflect.Copy`, `Value.Set/Len/Cap/Elem/Addr/IsNil` (`finalizeList`,
  `processListItem`, `growSlice`, `getNewItemFunc`), `v.Kind() != reflect.Slice`. Perennial's
  `reflect` is names only and has no specs (this repository has one trust-boundary spec,
  `Spec/reflect/ValueOf.lean`). Needs a model of `reflect.Value` over Goose's types (pointer to a
  struct implementing `runtime.Object`; a slice of such structs), or a fork rewriting the reflect
  use, or trust-boundary specs of these calls for the one object type the harness uses.
- **Standard-library calls with no spec in Perennial**: `strconv.ParseInt/ParseUint/FormatInt/
  FormatUint/ParseBool` (resource versions are decimal strings; this repo has `Spec/strconv/
  FormatUint`), `strings.HasSuffix/Contains/TrimSuffix/CutPrefix`, `strings.Builder.WriteString`,
  `fmt.Sprint/Sprintln/Fprintf`, `os.Getenv` (`watcher.go:70`, the `KUBE_PANIC_WATCH_DECODE_ERROR`
  variable), and the untranslated `encoding/json` (`Marshal`/`Unmarshal`: continue tokens,
  `continue.go:53,88`; health check), `encoding/base64` (`RawURLEncoding`, continue tokens),
  `path` (`Join`, `Clean`: `storage.PrepareKey`). Have specs: `strings.HasPrefix/TrimPrefix`,
  `bytes.Equal`, `errors.New/Is/As`, `fmt.Errorf/Sprintf`, `time`, `sync`, `sync/atomic`,
  `context.WithCancel`.
- **Names-only k8s functions on the unary path** (trust-boundary specs, most trivial): klog
  (`V`, `Errorf`, `InfoS`, ...: no-ops), `metrics.RecordEtcdRequest` and friends (no-ops),
  `tracing.Start` and the span's `AddEvent`, `audit.GetAuditIDTruncated`,
  `endpoints/request.TrackStorageLatency`, otel `attribute.String/Int`, feature gates
  (`DefaultFeatureGate.Enabled`: a fixed configuration), `meta.Accessor`, `meta.List`,
  `conversion.EnforcePtr`, `runtime.Encode/Decode/SetZeroValue`, apimachinery's error
  constructors (`NewBadRequest`, `NewResourceExpired`, ...), `fields`/`labels` `Set`/`Selector`
  (the predicates), `wait.JitterUntilWithContext` (the compactor), the `Codec` and `Transformer`
  interfaces (premises: decode inverts encode; the identity transformer).
- **Package initializers**: the new packages have none in `Proof/**/Init.lean`
  (`etc/gen-init.py`); a proof needs them.

## Open items

- Propose G1 and G3 to Perennial (independent branches off its `lean`), and decide G2 (Goose
  range-over-func support vs. a k8s fork).
- The watcher (`watcher.go`) translates but for `startWatching` (G1); not looked at further.
- The default `lake build` now builds these modules (the `EtcdGrove` globs): about 650 jobs, most
  of them cached; the new ones take a few minutes.
