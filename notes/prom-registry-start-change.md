# prometheus's default registry, route (b): the final trusted diff (for Upamanyu's sign-off, #15)

Branch `prom-registry` (notes/prom-registry.md, "Route (b)"). **Status: final** (2026-11-23, on `lean` at `82847d941b` with net-swap
landed, Perennial `70706ce5e`: the full build passes; `etc/tcb-report.py --check --update`). Parts 1-2 are as of
step 1 (commit `8168da033b`), but point 1, which `lean` has since settled; parts 3-5 are step 2's. Nothing lands
before sign-off.

## 1. Points for the sign-off

1. **`dto`'s initializer: settled on `lean`, no new axiom.** `Desc` is translated as a struct, and its field
   `constLabelPairs []*dto.LabelPair` needs client_model's `go` package (`dto`), so prometheus imports `dto` and
   its initializer runs `dto`'s. When step 1 was written, that added `dto`'s `opaqueInitsOk` and `initFuncsOk` to
   the trust base. Since then `lean` imports `dto` itself (prove-ps2-metrics: the metrics' `labelPairs`) and has
   made its variables goose `[[skip]]` entries and its `init()` a trusted no-op model
   (`TrustedCode/github_com/prometheus/client_model/go.lean`, prove-ps2-cminit, etcd-grove#32's pattern), so
   neither axiom exists. This branch takes `lean`'s `dto` unchanged.
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

## 3. Trust-boundary axioms (route (b) overall: steps 1 and 2)

Removed:
- prometheus's `initFuncsOk` (its `init.«0»`, now the trusted code above, stepped in its initializer's proof), and
  `defaultRegistry.init`, `DefaultRegisterer.init`, `DefaultGatherer.init` out of prometheus's `opaqueInitsOk`
  (translated) (step 1). Since lean's #23 (`d760b6e42a`) prometheus's other variables are goose `[[skip]]` entries
  and its `opaqueInitsOk` is gone; this branch takes the three registry variables off that skip list, since it
  translates their initializers;
- `EtcdGrove.prometheus.collectorName` (now a definition, `RegInv.lean`), `prometheus.MustRegister.wp_proof`,
  `prometheus.Register.wp_proof` (theorems over the real `(*Registry).MustRegister`/`Register`) (step 2, milestone 2);
- `EtcdGrove.prometheus.nameFree` (`Registry.lean`) and `EtcdGrove.prometheus.nameUnclaimed` (`Start.lean`)
  (milestone 3). With them the definitions `prometheus.namesUnclaimed`, `prometheus.namesFree`,
  `prometheus.descIdsDistinct` and `read.readRegPerm` are deleted.

Added: none. (Step 1 added client_model `dto`'s `opaqueInitsOk` and `initFuncsOk`; `lean` has since retired
both for its own `dto` import, point 1.)

`etc/tcb-report.py --check` against `lean`'s own baseline at `82847d941b` (net-swap landed), 2026-11-23: exactly
six axioms gone, none new: `prometheus.nameFree`, `prometheus.nameUnclaimed`, `prometheus.collectorName`,
`prometheus.MustRegister.wp_proof`, `prometheus.Register.wp_proof`, prometheus's `initFuncsOk` (baseline 366 to 360
entries). Collection `mvccfull`: the same, but `Register.wp_proof`, which it does not reach; `v3rpc`:
`prometheus.Register.wp_proof` gone. The other 49 collections unchanged.

Changed:
- `goose_adequacy_start` (part 4);
- `grpc_prometheus.NewServerMetrics.wp_proof`: its post gains `∃ ps ds, describes ⟨*ServerMetrics, m⟩ ps ∗
  ps ↦□ ds ∗ ⌜srvDescsOk (!os.isEmpty) ds⌝` (what providers/prometheus v1.1.0's `Describe` sends: the server
  metrics' descriptors, their names, IDs and validity) (milestone 2);
- the seven constructor axioms (`NewCounter`, `NewCounterVec`, `NewGauge`, `NewGaugeFunc`, `NewGaugeVec`,
  `NewHistogram`, `NewHistogramVec`): their posts' `⌜collectorName c n⌝` becomes `collectorName c n`, now a
  persistent `IProp` (`NewGaugeFunc`'s `⌜nameOk → collectorName⌝` becomes `(⌜nameOk⌝ → collectorName)`)
  (milestone 2).

## 4. `Proof/runtime/Start.lean`: removal only

net-swap (etcd-dist D2, landed on `lean`) removed the address part; this branch removes the names part. (A
separate branch, `single-process-restore`, restores the address part (`addrClaim`/`httpProtoFree` only): an
independent hunk, merged by whichever lands second.) Nothing is added to the statements (the file header gains a sentence saying the
names part is gone). Removed by this branch:
- `prometheus.nameFree n` from `startRights` (which becomes `startRights Ds`);
- `goose_adequacy_start`'s `Ns`, `hNs` and `hNsFree`, and `goose_adequacy_start_all`'s `hNsIds` (and its `Ns`,
  `hNs`, `hNsFree`);
- the axiom `prometheus.nameUnclaimed` and the definition `prometheus.namesUnclaimed` (and the file's import of
  `Registry.lean`).

Each closed proof makes its rights itself: inside its `Hwp`, it allocates a ghost map of the IDs its program's
packages register (`prometheus.regKeys_alloc`, `Proof/runtime/PkgInitRes.lean`, from the decided `regQsOk regQs`)
and makes its name the run's `PromRegGS`. The registry's invariant, built by that run's prometheus initializer,
owns every registered ID's element.

**Before** (`lean` at `82847d941b`, net-swap landed: only the names part is left):

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ns Ds : List GoString) : IProp GF :=
  iprop(([∗list] n ∈ Ns, prometheus.nameFree n) ∗ ([∗list] d ∈ Ds, dataDirFresh d) ∗
    envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ns Ds : List GoString) (hNs : Ns.Nodup) (hDs : Ds.Nodup)
    (hNsFree : prometheus.namesUnclaimed e Ns)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ns Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

theorem goose_adequacy_start_all ... -- the same binders, but
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState)))
    (hNsIds : prometheus.descIdsDistinct Ns := by decide +kernel) : ...

axiom prometheus.nameUnclaimed [GooseExts] (e : Expr) (n : GoString) : Prop
def prometheus.namesUnclaimed [GooseExts] (e : Expr) (Ns : List GoString) : Prop :=
  ∀ n ∈ Ns, prometheus.nameUnclaimed e n
```

(Before net-swap, `lean` at `aa1eb4da33`, `startRights` was `(Ns As Ds)` with `netAddrFree a` and
`httpProtoFree a` for each address, and the axiom also took `As`, `hAs`, `hAsLit` and `hAsFree : addrsUnclaimed e
As`: net-swap's part.)

**After** (this branch):

```lean
def startRights {GF : BundledGFunctors} [GooseExts] (Ds : List GoString) : IProp GF :=
  iprop(([∗list] d ∈ Ds, dataDirFresh d) ∗
    envVerifyOff)

axiom goose_adequacy_start [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ds : List GoString) (hDs : Ds.Nodup)
    (hDsFree : dataDirsAbsent e Ds) (hEnv : verifyEnvOff e)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok -∗ startRights (GF := GF) Ds ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2)

theorem goose_adequacy_start_all ... -- the same binders, but
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) : ...
```

## 5. The closed statements

The closed theorems that reached `namesUnclaimed` after net-swap (which retired `etcd/all`'s, `k8s/all`'s and
leaseexpiryN's) are mvccrand's and mvccfull's. Each loses exactly the binder
`(HNs : prometheus.namesUnclaimed (<program> r) <names>)` and gains nothing:

- `mvccrand_adequate`, `mvccrand_adequate_below` (`Proof/.../examples/mvccrand/Adequacy.lean`) and
  `mvccrand_robust.spec` (`Spec/.../examples/mvccrand/TopLevelRobustness.lean`) lose
  `(HNs : prometheus.namesUnclaimed (mvccrandProgram r) mvccrandNames)`;
- `mvccfull_adequate`, `mvccfull_adequate_below`, `Results.lean`'s `mvccfull_safe` and `mvccfull_robust.spec` lose
  `(HNs : prometheus.namesUnclaimed (mvccfullProgram r) mvccfullMetricNames)`;
- the name lists `mvccrandNames`, `mvccfullMetricNames` (`TopLevelDefs.lean`) are deleted, unused.

The distributed draft `etcd_robust.spec` (`examples/etcd/dist`, net-swap's rename of `etcd_dist_safe`; stated, not
proved) loses `(HNs : (∀ m ∈ d.members, prometheus.namesUnclaimed (serverProg d m) serverNames) ∧ ∀ w ∈
d.workloads, prometheus.namesUnclaimed (clientProg w (d.members.map Member.client)) clientNames)`, and its
placeholders `serverNames`/`clientNames` are deleted.

The generic etcdstart theorems that survive net-swap (`init_adequate_below`, `init_adequate`,
`init_adequate_start`) never took names. The WAL tester (`WalTester/`) has no closed adequacy theorem over its
initializer (its crash obligation, `tester_crash`, does not run initialization), so it needs no allocation.
