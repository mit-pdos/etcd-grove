# prometheus's default registry, route (b): the final trusted diff (for Upamanyu's sign-off, #15)

Branch `prom-registry` (notes/prom-registry.md, "Route (b)"). **Status: draft.** Parts 1-3 are final as of step 1
(commit `8168da033b` and after). Part 4 (`Start.lean`) and part 5 (the closed statements) are filled in once step 2
lands: step 2 proves `Register`/`MustRegister` over the real code and moves the closed proofs to rights each run
allocates itself. Nothing lands before sign-off.

## 1. Points for the sign-off

1. **New package-init axioms from `dto`.** `Desc` is translated as a struct, and its field
   `constLabelPairs []*dto.LabelPair` needs client_model's `go` package (`dto`). So prometheus now imports `dto`,
   which is translated types and names only (`Code/github_com/prometheus/client_model/go.toml`, no bodies, no
   imports). prometheus's initializer therefore runs `dto`'s, and the generated
   `Proof/github_com/prometheus/client_model/go/Init.lean` has the usual two trust-boundary axioms of a names-only
   protobuf package:
   - `github_com.prometheus.client_model.go.opaqueInitsOk`: its untranslated variable initializers
     (`MetricType_name`, `MetricType_value`, the file descriptor's variables) return without panicking;
   - `github_com.prometheus.client_model.go.initFuncsOk`: its `init()` (`file_..._metrics_proto_init()`, the
     protobuf type builder) returns.

   Both are true of the Go program: real prometheus imports `dto`, so Go runs these too. They are new entries in
   the trust base, the price of reading `Desc`'s fields. Alternatives:
   - trusted no-op models, as `proto`'s initializers have (`TrustedCode/google_golang_org/protobuf/proto.lean`).
     These would be more trusted code, against "init() the only trusted code";
   - leaving `Desc` opaque. That is not possible: `Register` reads `desc.id`, `desc.fqName`, `desc.dimHash` and
     `desc.err`.
2. **`NewDesc` is not translated.** desc.go's `NewDesc`, `V2.NewDesc`, `Desc.String` and `WithUnit` stay names
   only. Translated are `Desc` (the struct), `NewInvalidDesc` and `Desc.Err`. Translating the others would mean
   importing prometheus/common's `model`, prometheus's `internal` and cespare's `xxhash`. Their package variables
   compile regular expressions (`model.MetricNameRE`, `internal.GoCollectorDefaultRuntimeMetrics`, ...), so their
   untranslated initializers would join the trust base as further `opaqueInitsOk` axioms. And no verified program
   reaches `NewDesc`: the metric constructors that call it are names only, and their specs state what descriptor
   their collector describes (step 2: `collectorName`). So "desc.go with its bodies" is met for what `Register`
   reads, not for descriptor construction. `Desc.String` runs only inside `Register`'s `fmt.Errorf` error paths;
   with it names only, those paths are stuck, as the decision allows.

## 2. The trusted code: prometheus's `init()` (verbatim)

`Code/github_com/prometheus/client_golang/prometheus.toml`: `trusted = ["init.0"]`. It is the only trusted
declaration of the package; the registry (`NewRegistry`, `(*Registry).Register`, `(*Registry).MustRegister`,
`Register`, `MustRegister`, the variables `defaultRegistry`, `DefaultRegisterer`, `DefaultGatherer`) is the real
code, translated. Its replacement, `TrustedCode/github_com/prometheus/client_golang/prometheus.lean`:

```lean
/-
Trusted code for prometheus's client_golang v1.24.1 (`github.com/prometheus/client_golang/prometheus`;
`Code/github_com/prometheus/client_golang/prometheus.toml`): the package's `init()`, the one trusted
declaration of the package (Upamanyu's decision on mit-pdos/etcd-grove#15, 2026-11-22, route (b);
`notes/prom-registry.md`). The default registry itself is the real code, translated with its bodies:
`NewRegistry`, `(*Registry).Register`, `(*Registry).MustRegister`, `Register`, `MustRegister` and the
variables `defaultRegistry = NewRegistry()`, `DefaultRegisterer`, `DefaultGatherer`, which the package's
initializer runs before `init()`.

**What Go's `init()` does** (`registry.go:60-63`):

```go
func init() {
	MustRegister(NewProcessCollector(ProcessCollectorOpts{}))
	MustRegister(NewGoCollector())
}
```

`NewGoCollector` filters the toolchain's `runtime/metrics.All()` through package-level compiled regular
expressions and reads `runtime/metrics`; `NewProcessCollector` builds Linux's process descriptors. Neither
is translatable (and a stuck initializer would make every program stuck), so the model is the state the two
registrations leave in the (empty) default registry, written directly into its maps:

* `descIDs`: the 38 descriptor IDs the two collectors describe (`seed.descIDs`);
* `dimHashesByName`: their 38 fully-qualified names, each with its dimension hash (`seed.dims`);
* `collectorsByID`: the two collector IDs (the XOR of each collector's descriptor IDs, `seed.collectorIDs`).

**Why it is faithful.** `(*Registry).Register` (`registry.go:283-376`) on a registry whose descriptor IDs,
names and collector IDs are all new, which the two built-in collectors' are on the empty registry, takes
none of its error paths and ends by inserting exactly these keys (the collector ID, each new descriptor ID,
each new name with its dim hash); `MustRegister` then returns. So the maps' keys and the dim hashes are what
Go's `init()` leaves. The constants are those of configuration C (Linux, amd64, the pinned toolchain
`go1.27.3`, `etc/goose.py`'s `GO_TOOLCHAIN`: `go_info` carries the runtime's version as a const label, so its
descriptor ID, and the Go collector's ID, depend on it), measured against client_golang v1.24.1 and
re-checked by `examples/lib/prombuiltins`'s test (`TestSeedConstants`), which reads them from this file and
compares them with the real default registry's maps.

**Deviations, outside what verified code observes:**
- the values of `collectorsByID`: Go stores the two collectors (a `*processCollector`, a `*goCollector`),
  the model the nil `Collector`. A value is read only by `Register`'s `AlreadyRegisteredError` path (the
  collector ID already registered: excluded by every registration's rights), `Unregister` and the
  registry's `Gather`/`Collect`/`Describe` (not translated);
- the order of insertion, the maps' capacities, and the registry's lock, which the model does not take
  (Go's `MustRegister` takes and releases it): no other code can reach the registry while `init()` runs,
  since only prometheus's importers name it and they are initialized after it;
- what the collectors do besides registering (none: their constructors only build descriptors).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.all false

namespace Perennial
namespace github_com.prometheus.client_golang.prometheus

noncomputable section
variable [GooseExts] [GoGlobalContext]

/-- The descriptor IDs the process and Go collectors describe (configuration C). -/
def seed.descIDs : List w64 :=
  [0x512fd998710995b, 0x1656dbe17be56c8e, 0x25ecb62222d45656, 0x262eac1a08329894,
   0x27c54efad053ac38, 0x3344a85f7b6c8e8f, 0x370d8b8ba9508228, 0x3ae6afd8564ad088,
   0x3e79faf5f9128782, 0x411d6370a35c0ff3, 0x43ee38314d0e9d26, 0x4f8a790dd5db0ffd,
   0x5036f4e6bfcbacb3, 0x59cff99389bbcab8, 0x5dcc41232e6f6fcf, 0x685c04a736f2da00,
   0x69a5f00e0c426211, 0x6b4103ccc4d2326c, 0x70eb462430943cff, 0x769a93a32973af9b,
   0x80adfa8af06370e0, 0x87989ab99a809acc, 0x8b08ab44d6d64d78, 0x8ce99c9889b6fbce,
   0x8f317e9bd37b52b8, 0x9d3545e5f6f93ba5, 0x9ec03ad3db5d4289, 0xa85bf07416d4b8e0,
   0xac4ef85db62472cb, 0xc5ec13c9ed3ec103, 0xc87f9396f586162b, 0xd8075733a79d1e3a,
   0xd9589318aee2aa20, 0xdb617cf0bc600144, 0xe39410b0b2ace77d, 0xe6efe65b451f2f19,
   0xe7d1a41eea0bc77a, 0xe98ebbd01e4f623a]

/-- Their fully-qualified names (sorted), each with its dimension hash (configuration C). -/
def seed.dims : List (GoString × w64) :=
  [(go!"go_gc_duration_seconds", 0xf26f282174a16582),
   (go!"go_gc_gogc_percent", 0x6f193a898d82b57e),
   (go!"go_gc_gomemlimit_bytes", 0x3f946342ef3e2dc1),
   (go!"go_goroutines", 0xd6ea775f3e57e0a3),
   (go!"go_info", 0xd1ef65438edd64ca),
   (go!"go_memstats_alloc_bytes", 0xcb9e68d810ea886),
   (go!"go_memstats_alloc_bytes_total", 0x17cc9550218dfec4),
   (go!"go_memstats_buck_hash_sys_bytes", 0x7123dfe4d102ec69),
   (go!"go_memstats_frees_total", 0xc546633d5f4c2aee),
   (go!"go_memstats_gc_sys_bytes", 0x11ada46281e85a2),
   (go!"go_memstats_heap_alloc_bytes", 0x7c5deb187b85727),
   (go!"go_memstats_heap_idle_bytes", 0x4d92700b6179627e),
   (go!"go_memstats_heap_inuse_bytes", 0x5614f86bbcc71153),
   (go!"go_memstats_heap_objects", 0x4904e5a3507bc880),
   (go!"go_memstats_heap_released_bytes", 0xf36123dbdf6efbc9),
   (go!"go_memstats_heap_sys_bytes", 0xbd3e7caa8f21ce08),
   (go!"go_memstats_last_gc_time_seconds", 0x73a8a404a2b111fe),
   (go!"go_memstats_mallocs_total", 0x318b0ef37cbb1a3f),
   (go!"go_memstats_mcache_inuse_bytes", 0xf0f1c70cebad1075),
   (go!"go_memstats_mcache_sys_bytes", 0xad60f0b1578fc8c4),
   (go!"go_memstats_mspan_inuse_bytes", 0x245f1e59f37ed4a4),
   (go!"go_memstats_mspan_sys_bytes", 0xb85def6346437dc9),
   (go!"go_memstats_next_gc_bytes", 0x84369ece0eb7f645),
   (go!"go_memstats_other_sys_bytes", 0x60c4c92a200f4c53),
   (go!"go_memstats_stack_inuse_bytes", 0x9012115f6f8ae238),
   (go!"go_memstats_stack_sys_bytes", 0xf6a0e04a911cd1a),
   (go!"go_memstats_sys_bytes", 0xa5ff86d00c9ad67c),
   (go!"go_sched_gomaxprocs_threads", 0x1602c8428d1addf3),
   (go!"go_threads", 0xf559241e19ae5834),
   (go!"process_cpu_seconds_total", 0x7969c0480bf010ff),
   (go!"process_max_fds", 0xc40e6e0ce638254b),
   (go!"process_network_receive_bytes_total", 0xa804b284be1ced27),
   (go!"process_network_transmit_bytes_total", 0x5f99f2510c2201d7),
   (go!"process_open_fds", 0xdfd12ffdc6d1d772),
   (go!"process_resident_memory_bytes", 0xcfa21a2f3ba47cad),
   (go!"process_start_time_seconds", 0x9e3999b4a0663cbd),
   (go!"process_virtual_memory_bytes", 0xecb155a0ecaa6d63),
   (go!"process_virtual_memory_max_bytes", 0x59c47110ce47128e)]

/-- The two collectors' IDs (`*goCollector`, `*processCollector`; configuration C). -/
def seed.collectorIDs : List w64 :=
  [0x2af17207bfef49d7, 0x3c6db576c524bad7]

/-- The type `Registry` (the translation's `Registry.ty`, which this file cannot name: the translation
imports it). -/
@[reducible] def seed.Registry : go.GoType :=
  go.GoType.Named go!"github.com/prometheus/client_golang/prometheus.Registry" []

/-- The type `Collector` (the translation's `Collector.ty`). -/
@[reducible] def seed.Collector : go.GoType :=
  go.GoType.Named go!"github.com/prometheus/client_golang/prometheus.Collector" []

/-- `m[k] = v` for each `(k, v)` of the list, in order, for the map `m` (the argument): Go's `m[k] = v`
statements, as the translation writes them (`map.insert`). -/
def seed.insertAll (kt : go.GoType) : List (val × val) → val
  | [] => LamV "m" (Val #())
  | (k, v) :: rest =>
    LamV "m" (Seq (App (App (App (Val (map.insert kt)) (Var "m")) (Val k)) (Val v))
      (App (Val (seed.insertAll kt rest)) (Var "m")))

/-- **The package's `init()`** (see the file header): with `r := defaultRegistry` (set by
`defaultRegistry = NewRegistry()` before), `r.descIDs[id] = struct{}{}` for each built-in descriptor ID,
`r.dimHashesByName[name] = dimHash` for each built-in name, and `r.collectorsByID[id] = nil` for each
built-in collector ID (the nil `Collector`: see the file header). -/
def init.«0».impl : val :=
  (LamV BAnon
  (Seq (App (Val exceptionDo)
  (Let "r" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType seed.Registry))))
      (App (Val (GoInstruction (GlobalVarAddr go!"github.com/prometheus/client_golang/prometheus.defaultRegistry"))) (Val #())))
  (Seq (App (Val (seed.insertAll go.uint64 (seed.descIDs.map fun id => (#id, #()))))
    (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 (go.GoType.StructType [])))))
      (App (Val (GoInstruction (StructFieldRef seed.Registry go!"descIDs"))) (Var "r"))))
  (Seq (App (Val (seed.insertAll go.string (seed.dims.map fun nd => (#nd.1, #nd.2))))
    (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.string go.uint64))))
      (App (Val (GoInstruction (StructFieldRef seed.Registry go!"dimHashesByName"))) (Var "r"))))
  (Seq (App (Val (seed.insertAll go.uint64 (seed.collectorIDs.map fun id => (#id, #(interface.nil : GoInterface)))))
    (App (Val (GoInstruction (GoLoad (go.GoType.MapType go.uint64 seed.Collector))))
      (App (Val (GoInstruction (StructFieldRef seed.Registry go!"collectorsByID"))) (Var "r"))))
  (App (Val doExecute) (Val #())))))))
  (Val #())))

end

end github_com.prometheus.client_golang.prometheus
end Perennial
```

Evidence: `examples/lib/prombuiltins/seed_test.go` (`TestSeedConstants`) reads `seed.descIDs`, `seed.dims` and
`seed.collectorIDs` from this file. It requires go1.27.3, linux/amd64 and client_golang v1.24.1, and compares the
constants with the maps of the real default registry, and of a new registry with the two collectors registered
(`cd examples && GOTOOLCHAIN=go1.27.3 go test ./lib/prombuiltins/`). The test passes, and fails when a constant is
changed.

## 3. Trust-boundary axioms (step 1)

- Removed: prometheus's `initFuncsOk` (its `init.«0»`, now the trusted code above, stepped in its initializer's
  proof); `defaultRegistry.init`, `DefaultRegisterer.init` and `DefaultGatherer.init` out of prometheus's
  `opaqueInitsOk` (translated).
- Added: `dto`'s `opaqueInitsOk` and `initFuncsOk` (point 1).
- Still axioms until step 2: `EtcdGrove.prometheus.MustRegister.wp_proof`, `Register.wp_proof`,
  `collectorName`, `nameFree`.

## 4. `Proof/runtime/Start.lean`: removal only (step 2's last commit)

Removed, and nothing added:
- `prometheus.nameFree n` from `startRights` (which becomes `startRights As Ds`);
- `goose_adequacy_start`'s `Ns`, `hNs` and `hNsFree`, and `goose_adequacy_start_all`'s `hNsIds`;
- the axiom `prometheus.nameUnclaimed` and the definition `prometheus.namesUnclaimed`.

The old text (`lean`, today) follows. Each closed proof makes its rights itself: inside its `Hwp`, it allocates a
ghost map of the IDs its program's packages register. The registry's invariant, built by that run's prometheus
initializer, owns every registered ID's element.

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ns As Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] a ∈ As, netAddrFree a) ∗
    ([∗list] a ∈ As, httpProtoFree a) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    envVerifyOff)

axiom goose_adequacy_start ... (Ns As Ds : List GoString) (hNs : Ns.Nodup) (hAs : As.Nodup) (hDs : Ds.Nodup)
    (hAsLit : ...) (hNsFree : prometheus.namesUnclaimed e Ns) (hAsFree : addrsUnclaimed e As) ...
    (Hwp : ∀ [hG], ... -∗ threadTok -∗ startRights (GF := GF) Ns As Ds ={⊤}=∗ WP e ...) ...
```

## 5. The closed statements (filled in with step 2)

Expected: each closed theorem that passes names loses `HNs`/`Ns` (the `namesUnclaimed` premise:
`mvccfull_adequate`, `mvccrand_adequate`, the etcdstart family, the k8s and etcd examples' `TopLevelRobustness`)
and gains nothing. The exact before and after of each will be listed here.
