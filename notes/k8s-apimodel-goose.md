# The model API server's translation and proof (DaemonSet plan phase 3)

The model API server (`examples/k8sdaemonset/apimodel`, trusted Go, D50) translated by Goose and
given specs it is proved to meet. The specs are an internal layer of the controller's proof (D50's
last paragraph): the Go model stays the trust base. Status: `notes/k8s-daemonset-plan.md`, phase 3.

## The translation

- **Project `k8s-daemonset`** in `etc/goose.py`: the local module `examples/k8sdaemonset`, package
  `./apimodel`, with bodies (`Code/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel.lean`).
  `etc/goose.py --check` also checks that `examples/k8sdaemonset/go.mod`'s `k8s.io/{api,
  apimachinery,client-go}` are those of `examples/k8setcd3/go.mod` (`CLIENT_GO_PINS`), so the two
  projects translate one client-go.
- **Project `k8s-apiserver`, names and types only** (what the model's clients name): client-go's
  `kubernetes`, its 56 `kubernetes/typed/*` packages, `rest`, `discovery`, `applyconfigurations`'
  core, apps and autoscaling v1, `k8s.io/api`'s policy v1/v1beta1, authentication v1, autoscaling v1.
  `kubernetes.toml` and the typed core/apps tomls translate their types (`translate_types`, the
  structs excepted), so `kubernetes.Interface`, `CoreV1Interface`, `PodInterface`, ... are concrete
  interface types: the model's clientset converts to them.
- **Bodies added** (tomls): `metav1.ObjectMeta`'s accessors, `Now`, `Time.Equal`, the status
  reasons; `core/v1`'s and `apps/v1`'s `Get*`/`Set*` of the four types and the constants the
  create strategies use; `apierrors.NewBadRequest`, `NewResourceExpired`, `NewNotFound`,
  `NewAlreadyExists`; `watch` imports `runtime` (so `watch.Event` is concrete).
- **Embedded nil interfaces** (the clients embed client-go's interfaces, nil): translate; a method
  the model does not implement resolves through the nil interface and panics, as in Go.

## Gaps

- **C8 (closed 2026-10-28).** At Perennial `24bef275e`, Goose wrote an interface that embeds
  interfaces (`object`: `runtime.Object` and `metav1.Object`) with the embedded ones as type terms
  (`TypeElem [TypeTerm Object.ty]`), and the semantics' `typeSetContains` read a type term as that
  exact type, so `o.DeepCopyObject().(object)` (`copyObject`) panicked in the model where Go's
  assertion succeeds, and `copyObject.wp_proof` was a `sorry`. Fixed by `8ef540a62`, `d30f71f36`
  (an interface written as all its methods; method sets emitted): since the pin `ad74ee4f6`
  `copyObject` is proved, over `DeepCopyObject`'s spec per type
  (`Spec/k8s_io/api/{core,apps}/v1/*__DeepCopyObject.lean`) and each pointer type's membership in
  `object` (`go_type_set`).
- **C5 (from phase 1) reaches `prepareDaemonSet`.** `intstr.IntOrString` is axiomatized, so the
  create strategy's `intstr.FromInt32(1)` (an axiom, `Proof/k8s_io/apimachinery/pkg/util/intstr/
  FromInt32.lean`) and the allocation of an `IntOrString` have no spec; the deep values keep an
  `IntOrString` pointer's nil-ness only (`Proof/k8s_io/api/DeepBase.lean`). `prepareDaemonSet` is
  specified (`prepareDaemonSetD`: `MaxUnavailable`/`MaxSurge` set, their values opaque) and not
  proved.
- **Deep values** (`etc/gen-k8s-deep.py` -> `Proof/k8s_io/api/Deep.lean`): the 166 structs reachable
  from `Pod`, `Node`, `DaemonSet`, `ControllerRevision`, `ListOptions` and `DeleteOptions` as Lean
  values (`kd.*`) with deep ownership; opaque: `IntOrString` (C5), the `resource.Quantity` maps
  (must be nil), `RawExtension.Object` (nil), `FieldsV1`.
- **`time.Time.Equal`** is specified by Perennial as returning some `bool`: `daemonSetStatusEqual`
  compares the conditions' transition times with it, so `dsStatusMut` (UpdateStatus's mutation)
  allows a write whenever, and a write of nothing only when the status's other fields are equal.
- **A struct field through a fractional points-to**: Perennial's `wp_load` of a field needs the
  struct's points-to at fraction 1; the model's persistent configuration is stated field by field
  (`cfgAt`), and fractional structs are split by `iStructNamed` and recombined
  (`typedPointsto_combine`). Recorded in `notes/perennial-changes.md`.

## The proof

- **State** (`Proof/.../apimodel/State.lean`): `St` (the last version issued, the UIDs issued, per
  resource a `Table` of stored objects by key and the change log), `St.wf` (versions increase along
  each log and do not exceed `rev`; logged objects are the table's resource and carry their
  version and an issued UID; the stored objects are the log's replay), `St.le`, and the operations
  as functions of the state (`createApply`/`createErr`, `updateApply`/`updateErr`,
  `deleteApply`/`deleteErr`, `getObj`, `listOk`, `logStart`).
- **Specs** (`Spec/.../apimodel/`): each server operation logically atomic over `apiState γ σ`
  (`Defs.lean`: the clients' half of a history of states; the lock invariant holds the other half
  and the heap's state), with the outcome relation (`CreateOut`, `UpdateOut`, `DeleteOut`: a flagged
  failure, a check's error, or the write; reads at the state) and what the call returns
  (`writeRet`, `getRet`, `listRet`, `watchRet`). The failure premise is configuration: `mayHappen
  flag admin` (a flagged nondeterministic choice, never for admin clients); an ambiguous write
  (`Config.AmbiguousWrites`) may report a timeout after the write took effect.
- **Watch** (`watchRet`, `watchAt`, `evOk`, `watchCons`, `watchStartOk`, `runPre` in `Defs.lean`):
  400 for a field/label selector or `SendInitialEvents`, a flagged 500, 410 for a version not
  issued (or an older one when `ExpireWatches` is flagged), else a watch: a result channel (SPSC)
  each of whose events is a step of a cursor (`evStep`: an initial object, the next change in the
  namespace, or a bookmark when bookmarks are on and the client is not admin), started at the
  locked state's version for `""`/`"0"` (initial objects a `listOk` listing) or at the issued
  version given.
- **Proved** (`Link.lean`, `Results.lean`): `NewServer`, `create`, `get`, `list`, `update`,
  `remove`, `watch` (over `watcher.run`'s spec), `watcher.Stop`, `watcher.ResultChan` (and
  `nextRV`, `record`, `chance`, `rvString`, `newTable`, `podGrace`, `int32PtrEqual`), the typed
  clients' `Get`, `Create`, `List`, `UpdateStatus`, `Update`, `Delete`, `Watch` over them, the
  clientsets. **Not proved yet** (specified; the results over them take them as hypotheses,
  `links_pending`): the watcher's goroutine `run` (`send` has no spec: a `select` over the result
  and stop channels, both SPSC), `preparePod`, `prepareDaemonSet` (C5), `updateDaemonSetStatus`,
  `daemonSetStatusEqual`; `copyObject` is proved (C8, closed).
- **No infidelity found** in the model's Go code while proving it (the operations match `doc.go`).
