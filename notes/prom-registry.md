# prometheus's default registry as a trusted model on the Go heap (branch `prom-registry`)

The user's decision (kaashoek, 2026-11-22; mit-pdos/etcd-grove#15, the last two comments): replace
the prometheus registration axioms by a trusted model of client_golang v1.24.1's default registry on
the Go heap, so that a crash resetting the registry follows from the existing crash adequacy (each
run starts from `ownGoState ∅` and a fresh heap) with no new axiom. This note is the design as
built, what is done, and the plan for the rest (a handoff: the work spans sessions).

## Why

`nameFree n` (`Registry.lean`) is an opaque axiom tied to no Go state; `goose_adequacy_start` hands
it out once per name (`startRights`, premise `namesUnclaimed e Ns`). In a crash program (the WAL
tester, `wal-safe`'s `Hinit_wp`, whose initializer calls `MustRegister` three times per run) an
unused `nameFree n` can be carried through a crash frame and held twice in the next run. A registry
on the Go heap, with `nameFree` ghost state of the run, is empty again in every run for free.

## The design

### 1. The model: Go code, translated and verified, plus a small trusted glue

* **`examples/lib/promreg`** (Go, goose project `promreg`, translated with its bodies into
  `Code/github_com/mit_pdos/etcd_grove/examples/lib/promreg.lean`): client_golang's
  `Registry.Register` (`registry.go:283-376`) over descriptor *values* (`Desc{ID, FQName, DimHash,
  Invalid}`: what `Register` reads of each `*Desc`), with exactly the state that decides a later
  registration: `descIDs`, `dimHashesByName`, `collectorsByID` (a set), behind a `sync.Mutex`.
  `SeedBuiltins` adds the state client_golang's `init` leaves (the process and Go collectors on
  configuration C: Linux, amd64, Go 1.27.3; 38 descriptor IDs, 38 names with their dim hashes, 2
  collector IDs). Its code is verified, not trusted; what is trusted is its claim to be client_golang's
  registry, whose evidence is `examples/lib/promreg/model_test.go` (real registry and model side by
  side: `TestBuiltins` against the real default registry, `TestDecisions` one registration per check,
  `TestRandom` 200 runs of 30 random registrations, `TestMustRegister`, and `TestConstructorDescs`:
  the collectors etcd's constructors make describe one valid descriptor of ID `xxhash(n + "\xff")`).
* **The glue** (`TrustedCode/github_com/prometheus/client_golang/prometheus.lean`, trusted;
  `prometheus.toml`'s `trusted = ["Register", "MustRegister", "defaultRegistry", "init.0"]`):
  `defaultRegistry.init` allocates the variable and stores `promreg.NewRegistry()`; `init.«0»` is
  `SeedBuiltins`; `Register(c)` is `promreg.Register(collectorDescs(c))`, a non-nil error (a zero
  `AlreadyRegisteredError`) on a refusal; `MustRegister(cs...)` is Go's loop, panicking on an error.
  The bodies are what goose emits for the same Go (`notes/prom-registry.md`'s scratch package, not
  committed), with the names redirected. Deviations (the file header): error values, `Unregister`/
  `Gather` not modeled, the variable's type is the model's.
* **`collectorDescs`** (an `opaque val` of the glue: the model's one undefined operation): the
  descriptors `c.Describe` sends, as `promreg.Desc` values, in a new slice. Its meaning on a
  collector is what the collector's constructor says.

**Why a Go package and an opaque `collectorDescs`, not a model reading the collector.** The
collectors are made by names-only constructors (axioms, which stay), and `Desc`, `Registry` and the
collector types are opaque in the translation (their fields name `client_model` types the
configuration does not import). A model cannot read a descriptor's ID from the heap; something must
say what a constructed collector describes, and that is what the constructors' specs already say
(`collectorName c n`). So:

### 2. `collectorName` becomes a definition (pure, no constructor statement changes)

`collectorName c n : Prop` := there is a dim hash `dh` such that, in every instance of the logic,
`collectorDescs c` returns a new slice holding the one descriptor `⟨descId n, n, dh, false⟩`
(`⊢ {{ True }} collectorDescs.impl c {{ (s), RET #s; s ↦* [desc] }}`, quantified over `GF`/`hG`, so
still a `Prop`). The constructor axioms (`NewCounter`, ...) keep their statements: they now claim
this triple of their result, which is what `TestConstructorDescs` checks. (`collectorName` gains the
semantics' instance arguments; it loses its `axiom`.) `descId` is unchanged.

### 3. `nameFree` becomes ghost state of the run

* **The ghost names** `class PromRegGS (GF) where γ : GName` (as `WalGS`): a ghost map from IDs
  (`w64`) to `()` in the universal camera (`AllG`, so no `GF` changes and no closed statement
  changes). An instance is allocated in each run (by the closed theorem's proof, inside the WP of
  `goose_adequacy*`), so a crash's next run has a fresh one: the reset is the crash adequacy's.
  No agreement trick ties a ghost name to a location (Perennial has no `meta` tokens), so the name
  is a typeclass, as `WalGS`'s; the ~115 users of `nameFree` get the instance in their sections.
* `nameFree n := ⌜n ∉ promreg.builtinNames⌝ ∗ descId n ↪[γ] ()` (the ID's exclusive element).
* **Allocation** `promReg_alloc Ns (hNs) : ⊢ |==> ∃ _ : PromRegGS GF, builtinToks ∗ namesFree Ns`
  for `Ns` whose IDs are pairwise distinct, not built in, and whose names are not built in (decided
  by the kernel, as `descIdsDistinct` is today). `builtinToks`: the elements of the 38 builtin IDs and
  the 2 collector IDs.
* **The registry invariant** (`promreg`'s proofs): the mutex's invariant owns the maps and the
  elements of every registered descriptor ID and collector ID, and every registered name is built
  in or has its ID registered. Holding `nameFree n` then excludes `descId n` from both ID sets and
  `n` from the names (an element held twice is invalid), which is what `Register` needs to succeed.
* **`isPkgInit prometheus`** := `∃ l, globalAddr defaultRegistry ↦□ l ∗ promreg.isRegistry l γ`.
  Its initializer takes `builtinToks` (an entry of `ownInitResL`'s list, as the registering packages'
  `namesFree regNames`) and gives it to the invariant when `SeedBuiltins` runs.

### 4. The specs, now theorems

* `MustRegister.spec`: gains `[PromRegGS GF]` and `isPkgInit prometheus` in its precondition
  (persistent); otherwise the same. Proof: the glue's loop over one collector, `collectorName`'s
  triple, `promreg.Register`'s spec.
* `Register.spec` (grpc-prometheus's server metrics, `getServerMetrics`): its collector describes the
  server metrics' descriptors (2 or 4 counter vectors and, with the histogram option, one histogram
  vector): the spec takes their rights (`namesFree grpcSrvNames` and the element of their collector
  ID, the XOR) and `NewServerMetrics`' axiom says what the collector describes (a multi-descriptor
  `collectorNames m Ns`, as `collectorName`). This is the part of `namesUnclaimed` that was about
  grpc-prometheus's names. **Open**: `NewServerMetrics.spec` is in #24's area (grpc), and its options
  decide the descriptors (`promSrvMetricsOpt`).
* The package initializer: `opaqueInitsOk` loses `defaultRegistry.init` (modeled); `initFuncsOk`
  goes (its only member, `init.«0»`, is modeled). The others (`DefaultRegisterer`,
  `DefaultGatherer`, ...) keep `opaqueInitsOk`.

### 5. `goose_adequacy_start` shrinks

`Ns`, `hNs`, `hNsFree`/`namesUnclaimed`, `hNsIds` and the names of `startRights` go, with
`prometheus.nameUnclaimed`/`namesUnclaimed`. The closed theorems lose exactly those premises
(`mvccfull_adequate`'s `HNs`, ...). What stays of "untranslated code registers nothing extra" is a
claim about specific untranslated code, now carried by its own specs: every untranslated function or
initializer of a program's closure that could register with the default registry. Through the model,
an untranslated function's call of `MustRegister`/`Register` would run the model (the trusted
functions are the model's whatever calls them), but an untranslated function's body is unconstrained,
so its spec (an axiom) is the claim: `initFuncsOk`/`opaqueInitsOk` of names-only packages and the
names-only functions' axioms must not hide a registration. The list (from the pinned etcd's sources:
`prometheus.MustRegister`/`Register` in a package translated names only, or in an untranslated
`init`) is the next stage's first task; each found goes into that spec's docstring (or its
precondition takes the rights).

First pass (2026-11-22, etcd `d7c7f64`): the etcd packages that register with the default registry
are `auth`, `etcdmain`, `etcdserver`, `api/{etcdhttp,membership,rafthttp,snap,v2store,v3rpc}`,
`apply`, `read`, `txn`, `lease`, `proxy/grpcproxy`, `storage`, `storage/{backend,mvcc,wal}`. Those
with a generated `Init` take their rights (`regNames`); `etcdhttp`, `v2store`, `etcdmain` and
`grpcproxy` have none (outside every verified closure, to confirm per program). Runtime
registrations: `v3rpc.getServerMetrics` (translated: `Register.spec`, decision 3),
`etcdserver.EnableAllRuntimeMetrics` and `v2store`'s `Register(readCounter)` (names only, called
from `embed`/`v2store`, to confirm unreached). k8s component-base's `legacyregistry` (the k8s
examples): its `init` registers the process and Go collectors in its **own** `KubeRegistry`, not
the default registry; `Handler`/`HandlerWithReset` (promhttp's `InstrumentMetricHandler` registers
`promhttp_metric_handler_requests_*` with `prometheus.DefaultRegisterer`), `CustomRegister` and
`CustomMustRegister` do register with it, but no translated code calls them (`Code/`: only their
names); their names-only specs, if any is ever given, must take the rights.

### 6. Threading through package initialization (`etc/gen-init.py`)

Today every registering package's `wp_initialize'` takes `namesFree regNames` through
`ownInitResL`'s list (`regResL`), and prometheus's init is a `_lb` form with no resource. New:
prometheus is a package with a resource (`builtinToks`) in that list, its init its `_res` form; the
generated `Init`/`InitLinked` files get `[PromRegGS GF]` in their sections, and `MustRegister`'s
applications pass `isPkgInit prometheus` (from the imports' facts). The closed theorems allocate
`PromRegGS` (`promReg_alloc` of their program's names, the list they pass as `Ns` today) and hand
`builtinToks ∗ namesFree Ns` to the init chain where `startRights` handed `namesFree Ns`.

## Status (2026-11-22)

Done (committed on `prom-registry`):
1. The Go model and its evidence (`examples/lib/promreg`), goose project `promreg`, its translation.
2. The glue (`TrustedCode/.../prometheus.lean`) and `prometheus.toml`'s `trusted` list; the
   translation regenerated with them (see STATUS).

Next, in order:
3. `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/`: `PromRegGS`, the tokens,
   `promReg_alloc`, `isRegistry`, and the specs of `NewRegistry`, `SeedBuiltins`, `Register` (the loop
   over the descriptors with the three maps; a general spec for descriptors whose IDs are their
   names' `descId`s, names not built in, with the elements of their IDs and collector ID).
4. `Registry.lean`: `collectorName`, `nameFree` as definitions; `MustRegister.lean`, `Register.lean`,
   `Init.lean` (prometheus's `wp_initialize'_res`) as theorems; `PkgInit.lean`'s `isPkgInit`.
5. `etc/gen-init.py` (prometheus a resource package; the instance in the sections), regenerate;
   `Proof/runtime/Start.lean` (drop the names); the closed theorems (mvccfull, mvccrand, etcdstart's
   `Adequacy`/`AdequacyMembers`/`StartRes`, the examples' Results/TopLevelRobustness) allocate the
   instance; `notes/decisions.md` (supersede D19d's names part), `notes/axiom-review/`.
6. The residue list (§5), `Register.spec`'s grpc rights (§4), gates, `tcb-report --check --update`,
   the collections' `--update`.
