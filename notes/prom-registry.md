# prometheus's default registry as a trusted model on the Go heap (branch `prom-registry`)

**Superseded in part (2026-11-22, route (b), the last section "Route (b)")**: the Go model
`examples/lib/promreg`, its glue and its proofs are retired; client_golang's real `registry.go`/`desc.go` are
translated and prometheus's `init()` is the only trusted code. The sections below are the record of
route (a) and of the ghost-name question (Option 4 survives).

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

3. (statements) `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Defs.lean`: `PromRegGS`,
   `idTok`/`idToks`, the builtin lists (`builtinKeys_nodup` by `decide`), `descKeys`, `descsOk`,
   `regInv`, `isRegistry`; `Spec/.../examples/lib/promreg/{NewRegistry,Registry__SeedBuiltins,
   Registry__Register}.lean`. `notes/prom-registry-start-change.md`: the start model's change, for
   Upamanyu's sign-off (posted on #15 by the coordinator; nothing lands before it).

3'. (2026-11-22, done) The proofs of the three specs and `promReg_alloc` (see "Handoff" below).

Next, in order (stage 4 on is blocked: "Handoff"):
3'. The proofs of the three specs (`Proof/.../promreg/{NewRegistry,Registry__SeedBuiltins,
   Registry__Register}.lean`; `Register`'s loop: invariant over the prefix of `ds` seen, with
   `newSeen`/`newDims` mirroring `descKeys`/the names; the tokens give `descIDs !! id = none`,
   `collectorsByID !! xor = none` and the names absent), `promReg_alloc` (`ghost_map_alloc` of the
   builtin keys and the program's names' IDs), and whether the specs need `isPkgInit promreg`
   (the glue initializes the package in `defaultRegistry.init`; gen-init must then generate
   promreg's `PkgInit`/`Init`).
4. `Registry.lean`: `collectorName`, `nameFree` as definitions; `MustRegister.lean`, `Register.lean`,
   `Init.lean` (prometheus's `wp_initialize'_res`) as theorems; `PkgInit.lean`'s `isPkgInit`.
5. `etc/gen-init.py` (prometheus a resource package; the instance in the sections), regenerate;
   `Proof/runtime/Start.lean` (drop the names); the closed theorems (mvccfull, mvccrand, etcdstart's
   `Adequacy`/`AdequacyMembers`/`StartRes`, the examples' Results/TopLevelRobustness) allocate the
   instance; `notes/decisions.md` (supersede D19d's names part), `notes/axiom-review/`.
6. The residue list (§5, first pass done), `Register.spec`'s grpc rights (§4; the coordinator's
   instruction, 2026-11-22: #24 has not answered, so add to `NewServerMetrics`' post the clause that
   the collector describes the server metrics' descriptors (`collectorDescs` of `m`, as
   `collectorName`), its statement otherwise unchanged, and flag it; needs stage 4's definition), gates, `tcb-report --check --update`,
   the collections' `--update`.

## Handoff (2026-11-22, end of the session that proved stage 3')

**Done** (commits `6ddb44f707`, `2c0bbcd8f6`): `Proof/github_com/mit_pdos/etcd_grove/examples/lib/promreg/`
`NewRegistry.lean`, `Registry__SeedBuiltins.lean` (with `wp_Builtin{IDs,Dims,Names,Collectors}`, the slice
literals), `Registry__Register.lean` (the loop's state is pure: `pIDs ds j`, the `eraseDups` of the prefix's IDs,
`xorAll` of it, the seen set, the names; the rights are checked absent from the registry before the loop,
`regToks_absent_all`, and handed over after the commit loops, `regToks_insertAll`, the final maps equal to
`insertAll (descKeys ds) (ids ∪ cols)`). `Defs.lean` gained the package's fact (`isPkgInit promreg`, `True`; its
`IsPkgInit` instance is in `Defs.lean`, where `etc/gen-init.py`'s `instances()` finds it), `idToks_cons`/`_app`,
`idTok_excl`, `regToks_absent`/`_insert`, `builtinToks_split`, `union_insert_l`/`_r`, `promReg_alloc` (for any
`ks` with `(builtinKeys ++ ks).Nodup`). The three specs take `isPkgInit promreg` (the glue's `defaultRegistry.init`
initializes the package before `NewRegistry`): **decided yes**. Not yet in a `Link` (promreg has no callers'
`Link` yet); built with `etc/lean-check.py` only (no `lake build` run on the branch since).

**Names** (the coordinator, 2026-11-22): the new defined right is to be `prometheus.regFree` (not yet written);
the opaque `prometheus.nameFree` axiom stays until the `goose_adequacy_start` shrink, which is to be the last
commit of stage 5 (dropped if Upamanyu declines on #15; the fallback is the axiom unchanged and the closed
proofs at `Ns := []`).

**Blocked: where the run's ghost name lives.** §3/§4 make `isPkgInit prometheus` `∃ l, globalAddr
defaultRegistry ↦□ l ∗ isRegistry descId l`, whose `isRegistry` names the instance `PromRegGS GF` (its `γ`).
Perennial's `define_is_pkg_init` builds a package's `IsPkgInit` instance by synthesizing the `IsPkgInit`
instances of its imports (`Pkg.lean`, `isPkgInitDeps`), so every package above prometheus would get the
instance argument, and every module that elaborates their `isPkgInit` or applies a theorem stated over them
would need `[PromRegGS GF]` in scope: 52 packages above prometheus (gen-init's inventory), 2073 modules naming
them (`Proof`, `Spec`, the parts), and their importers' theorems gain the argument. §3's "the ~115 users of
`nameFree` get the instance" missed this. Section variables would also add the instance to every theorem of
those sections (it depends only on `GF`), closed statements included where they sit in such a section.
An existential name in the fact (`∃ l γ, … isRegistry γ l`) does not work: nothing ties it to the name of the
rights a caller holds (the rights are allocated before the registry exists, and the fact is the only thing the
registering packages' initializers learn of prometheus's). Every way around found needs a name both sides
can write, that is fresh in each run:

1. **The instance everywhere, by script**: `variable [promG : promreg.PromRegGS GF]` in every section of the
   modules above prometheus (and the generated `Init`/`InitLinked`), the closed proofs giving it from
   `promReg_alloc`. As designed, no Perennial change; a diff over thousands of files, conflicting with every
   session in the server's cone, and every closed statement must be checked not to gain the argument.
2. **A per-generation ghost-name supply in Perennial** (built in `GoStateGS`, "Option 2": a name allocated by the adequacy
   theorems at each generation's start, for a client's own ghost map, as `packageMonoName` is for the package
   state): `PromRegGS` becomes a definition from `hG`, in scope wherever `hG` is; no ripple. A Perennial
   change (general: any package fact about per-run ghost state needs it), to be proposed on its own
   (`notes/perennial-changes.md`).
3. **The registry's ghost state as an extension's local ghost state** (`Exts.LocalGS`, per generation, in
   `hG`): no Perennial change, but a new trusted extension (its `extsLocalStart` given by the start model).

The registry and its proofs do not depend on the choice (they are generic in `PromRegGS`). Until it is made,
stage 4 (`collectorName`/`regFree` definitions, `MustRegister`/`Register`/the initializer as theorems,
`NewServerMetrics`' clause) and stage 5 (gen-init, the closed proofs) wait; `collectorName` as a definition
(§2) does not depend on it and could go first, but rebuilds everything above `Registry.lean`.

## Step A (2026-11-22): Perennial's package machinery cannot supply the run's γ

The user's decision (kaashoek, 2026-11-22): before any Perennial change, check whether Perennial's existing
per-run package-state ghost machinery can record the registry's ghost name `γ` for the run, persistently and
with agreement, readable by `isPkgInit prometheus` and by the rights, without a typeclass. **It cannot.**
Read at the pin (`/shared/perennial-c14cca87a`, `c14cca87a`):

* **What a generation hands the program.** Every adequacy theorem's WP premise receives
  `extsGlobalStart`, `extsLocalStart`, `ownGoState σ.goState.packageState` (`∅`) and `threadTok`
  (`InitAdequacy.lean` `goose_adequacy_init`; `CrashAdequacy.lean` `goose_crash_adequacy`'s `Hstart` and its
  crash continuation, which gets `ownGoState (hG := L'.goose_go_stateGS) ∅`); this repository's
  `goose_adequacy_start` adds `startRights`. The per-generation ghost names are the fields of `GooseLocalGS`
  (`Lifting.lean:738`): the extensions' `LocalGS`, `goose_na_heapGS` (`naHeapName`), `goose_go_stateGS`
  (`packageInitedName`, `packageMonoName`), `goose_threadGS` (`threadTokName`), `goose_crashGS` (`crashName`).
  None has room for a client's entry:
  - `packageInitedName`: `ghost_var` halves of the *physical* package state, the other half in the state
    interpretation (`gooseStateInterp`: `ownGoStateCtx σ.1.goState.packageState`). An entry changes only by
    the `PackageInitStart`/`PackageInitFinish` instructions (`ownGoState_update_start`/`_finish`,
    `PostLifting.lean` `wp_GoInstruction'`), whose package names come from the program's code: a proof cannot
    add a key "no Go package uses".
  - `packageMonoName`: `ownGoState v` holds `ghostMapAuth packageMonoName 1 (initedOf v)`, its map pinned to
    the `true` entries of that same physical map (`Lifting.lean:304`), its fragments `p ↪□ b` with `b : Bool`.
    Even a key the proof could set would give no agreement on a `γ`: a name encoded in keys (`"γ:" ++ γ ↪□
    true`) is a set of persistent facts, two of which never conflict, so nothing says "this γ and no other".
  - `naHeapName`: the heap's points-to's, tied to the physical heap; no `meta` tokens (`Algebra/NaHeap.lean:9`:
    "no per-location metadata"), so no ghost name attaches to a location. (And `globalAddr defaultRegistry`
    is a static address, `GoSemanticsFunctions.globalAddr`, allocated only by prometheus's own
    `GlobalAlloc` (`wp_GlobalAlloc`), after the rights must already exist.)
  - `threadTokName`, `crashName`: fixed contents (`ThreadGS`: the slot tokens below `threadBound`;
    `CrashGS`: `notCrashed`/`crashed`), their authorities in the state interpretation.
* **The universal camera does not give a second slot at an existing name.** `own γ (a : A)` owns the
  singleton `{[e := some a]}` of `∏ e, option (int e)` (`Ghost/All.lean`), so the other codes at
  `packageMonoName` are logically free; but putting `some x` there from `ε` is frame-preserving only for an
  `x` compatible with every frame, which an agreement (or exclusive) element is not. The update that is
  frame-preserving (a fresh key of a `gmapUR`, as `own_alloc_strong`) chooses the key, which readers then
  cannot name: the same problem one level down.
* **`IsPkgInit` cannot carry a run-chosen value.** `isPkgInitDef prometheus` is a fixed proposition of a
  global instance (`Pkg.lean:148`); `ownInitializing g` records `□ g pkg` for every initialized `pkg`, with
  `g pkg = isPkgInit pkg` forced by `GetIsPkgInitProp` (`build_get_is_pkg_init_wf`). So the record holds
  `∃ γ, P γ` at best, and two such facts agree on `γ` only if `P` contains an agreement at a name both sides
  can write, which is the question again. With `P γ := globalAddr defaultRegistry ↦□ l ∗ isRegistry γ l` the
  heap gives agreement on `l` (persistent points-to's), not on `γ` (two lock invariants on one mutex do not
  identify their ghost names).
* **Rights minted by prometheus's initializer do not get around it.** The rights could carry the registry
  fact themselves (`regFree n := ∃ γ l, globalAddr defaultRegistry ↦□ l ∗ isRegistry γ l ∗ idTok γ (descId
  n)`), which needs no agreement on `γ` (`MustRegister` uses the right's own `isRegistry`). But prometheus's
  initializer would then have to hand each registering package `q` its rights, and the only route into
  `q`'s initializer is `ownInitResL`'s entries, which the closed proof fixes at the start, before `γ`
  exists. A claim from an invariant in prometheus's fact (`q`'s tokens, unclaimed or claimed) needs a
  per-run, per-`q` exclusive witness that refutes a second claim; the package state offers only `σ !! q =
  some false` (held by any proof holding `ownGoState` during `q`'s initialization, not persistent) and
  `q ↪[packageMonoName]□ true` (only after `q` finishes, too late), so the claim lemma is not provable.

**Crash soundness** is not the obstacle (every per-generation name above is fresh in each generation:
`goose_crash_step` allocates the heap, the package state, the thread and crash tokens anew); the obstacle is
that no per-generation ghost location is free for a client, and every agreement needs one.

So option 1 (the instance everywhere), option 2 (Perennial) or option 3 (a new trusted extension) remain;
the user's decision picks option 2 next. Its design follows; nothing is changed in Perennial.

## Option 2: a per-generation ghost-name supply in Perennial (design, for review)

**Lean shape** (Perennial, mit-pdos/perennial#681, branch `local-names`; `GooseLang/LocalNames.lean`):

```lean
class GoStateGS (GF : BundledGFunctors) where
  ...                                -- unchanged fields
  localNamesName : GName             -- the generation's supply, with the package state

variable {GF : BundledGFunctors} [hG : GoStateGS GF]

def ownLocalNames (m : GMap GoString GName) : IProp GF     -- exclusive authority
def localName (k : GoString) (γ : GName) : IProp GF         -- persistent record
theorem localName_agree (k) (γ γ') : ⊢ localName k γ -∗ localName k γ' -∗ ⌜γ = γ'⌝
theorem localName_set {m} {k} (h : m !! k = none) (γ) :
    ⊢ ownLocalNames m ==∗ ownLocalNames (<[k := γ]> m) ∗ localName k γ
```

**The name lives in `GoStateGS`, not in a new `GooseLocalGS` field** (as first designed here): clients
rebuild `GooseLocalGS` with its six-field anonymous constructor to substitute the Go context (Perennial's
crashfs, netfs, `NotCrashedChanTest`, and this repository), and a seventh field broke them all, while they
keep `GoStateGS` opaque. `GoStateGS` is per generation (it holds `packageInitedName`/`packageMonoName`),
allocated afresh by `goose_crash_step`, so the supply is per generation as designed.

(`GoString` and `GName = Nat` are `Pos.Countable`; the keys are strings so that a library names its entry
by its package path, as the package state does.)

**Which adequacy theorems change.** Every theorem that builds a `GooseLocalGS` allocates the name
(`localNames_init`) beside the package state (`goose_init`, `goose_local_init`, `goose_crash_step`, as
`_localNames` variants), and each
returns `ownLocalNames ∅` of the new generation with its `ownGoState`. The resource reaches the program in new variants (`_localNames`) whose WP premises take
`ownLocalNames ∅` after `ownGoState …` (and the crash continuations the next generation's after
`ownGoState (hG := L'.goose_go_stateGS) ∅`): `goose_adequacy`, `goose_adequacy_below`, `goose_invariance`,
`goose_crash_adequacy`, `goose_dist_adequacy`, `goose_dist_crash_adequacy`,
`goose_dist_mixed_crash_adequacy` and their `_init` wrappers. To spare every existing client, each keeps its
statement and becomes a corollary of its variant (the extra premise dropped with `-∗`), so the change is
additive. Changed in place (#681): `crashFrame` (and `BootWp`, `dist_crash_*`), `goState_init`,
`goStateGSUpdatePre`/`goStateGSUpdate` (one more name).

**In this repository** (after a pin bump that brings it): `goose_adequacy_start` (`Proof/runtime/Start.lean`,
the trusted start model) gets `ownLocalNames ∅` in its WP premise, a resource Perennial's theorems now give
(one more item for Upamanyu's sign-off on #15, `notes/prom-registry-start-change.md`), as do the crash
wrappers (`fsSQ_crash_adequacyShared`, ...) that the WAL tester's crash proof uses. Then, with `promKey :=
"github.com/prometheus/client_golang/prometheus"`:

* `PromRegGS` goes; `isRegistry γ l`, `idTok γ`, `regInv γ` take `γ` explicitly (they already do inside).
  `localName` reads the name from `GoStateGS`, in scope wherever `hG` is.
* `prometheus.regFree n := ⌜n ∉ builtinNames⌝ ∗ ∃ γ, localName promKey γ ∗ idTok γ (descId n)`.
* `isPkgInitDef prometheus := ∃ l γ, globalAddr defaultRegistry ↦□ l ∗ localName promKey γ ∗ isRegistry γ l`.
* `MustRegister`'s proof: the fact's `γ` and the right's `γ'` are equal by `localName_agree`, then
  `Registry.Register`'s spec. No instance argument appears anywhere: `localName` reads the name from `hG`.
* The closed proof, per run: `promReg_alloc` (fresh `γ`, `builtinToks γ ∗ idToks γ ks`), `localName_set
  promKey γ` (from `ownLocalNames ∅`), and hands `builtinToks` to prometheus's initializer and the
  `regFree`s to the registering packages through `ownInitResL`, as `startRights` hands `namesFree` today.

**The crash argument.** `localName` reads `GoStateGS.localNamesName` (of `hG.goose_localGS.goose_go_stateGS`), allocated fresh for each
generation (`goose_crash_step_localNames`), and the generation's program alone holds its authority, `∅` at its start. A
`regFree` or a prometheus fact carried through a crash frame is over the crashed generation's `L` (its
`localName`, `idTok` and registry are the old ones) and is not the new generation's `regFree`, which every
spec of the new run is stated over; the new run's `γ` is set once (`localName_set` needs the key absent, and
the authority starts at `∅`), so every reader of the new run agrees on it.

**Why it is general, not shaped by this proof.** It is the Lean port's missing counterpart of what Rocq's
Iris gives through `gen_heap`'s `meta` tokens: a way to make per-generation ghost state that package-level
facts (`isPkgInit`) can name. Without it, any package whose fact must name ghost state of the run
(a package-level registry or table behind a global variable, a ghost model of a package variable whose
resources are handed out before the package initializes) must either thread a typeclass instance through
every importer's `isPkgInit` (`define_is_pkg_init` synthesizes the dependencies' instances, so the
argument spreads to every package above it) or become a trusted extension. The supply is keyed by strings
so that any number of packages use it, and it changes no existing statement. (`meta` tokens on the heap
would not serve here: the registry's location is allocated by prometheus's initializer, after the rights
must exist.)

**Rejected variants.** The authority inside `ownGoState` (an existential map, so no adequacy statement
changes): a proof could not know a key is unset at the start, so `localName_set` would have no premise to
discharge. A name recorded per package at its `PackageInitStart` (the map's domain following the package
state's): the rights must name `γ` before prometheus starts, so this would need the claim scheme above, with
a per-package exclusive token deposited at the start; more machinery for the same result.

**Status.** Built: mit-pdos/perennial#681 (branch `local-names`), on etcd-grove's pin as `local-names-c14`
(`8dd458684`, worktree `/shared/perennial-local-names-c14`, manifest `/shared/tmp/manifest-ln14.json`). Stages 4–5
are built against it.

## Stage 4 started; blocked on the model's `Assumptions` (2026-11-22, session on perennial#681)

**Done** (built against `/shared/tmp/manifest-ln14.json`, `local-names-c14`):
* `PromRegGS` is gone: the promreg ghost state takes its name explicitly (`idTok γ k`, `idToks γ ks`,
  `builtinToks γ`, `regInv γ f …`, `isRegistry γ f r`; the lemmas take `γ` implicitly), the three specs
  quantify `∀ γ`, `promReg_alloc` gives `∃ γ, builtinToks γ ∗ idToks γ ks`. Proofs rebuilt.
* `Registry.lean`: `promKey`, `nameDesc n dh`, `collectorDescsAre c ds` (the glue's `collectorDescs.impl`
  returns `ds` in a new slice, in every instance: `∀ GF hG sem`), **`collectorName` a definition** (`∃ dh,
  collectorDescsAre c [nameDesc n dh]`; the constructor axioms unchanged in text), and **`regFree n`**
  (`⌜n ∉ builtinNames⌝ ∗ ∃ γ, localName promKey γ ∗ idTok γ (descId n)`). The `nameFree` axiom stays
  (Start.lean). Built through `read/Init`, `MustRegister`, `NewCounterVec`.

**Blocked: the glue resolves the model's functions by name, and no closed theorem assumes them.**
The glue (`TrustedCode/.../prometheus.lean`) calls `FuncResolve promreg.NewRegistry` and
`MethodResolve *promreg.Registry "Register"/"SeedBuiltins"`, and the model's bodies resolve
`promreg.Builtin*` and `sync.Mutex`'s methods. Stepping a resolution needs its `FuncUnfold`/`MethodUnfold`
(Perennial `PostLang.lean`: `#(functions f ts) = impl`), which only `promreg.Assumptions` (and
`sync.Assumptions`) give. `prometheus.Assumptions` has only `import_time_Assumption` (the translation's
imports are `["!*", "time"]`, and client_golang does not import the model), so neither `MustRegister`'s
proof nor prometheus's initializer (the glue's `defaultRegistry.init`) can step into the model, and the
instance would have to come from the closed theorems, whose `Assumptions` arguments (`package_sem`,
`mvcc_sem`, …) are part of their statements. The same gap makes `isPkgInit prometheus`'s dependency on
`promreg` (needed for `sync`'s fact) absent from `GetIsPkgInitWf`; that part alone is fixable (a
hand-written instance with dependencies `[time, promreg]`, `etc/gen-init.py` following it), but not the
`Assumptions`.

**Soundness hazard on the branch as it stands** (not landed): prometheus's `Init.lean` predates the glue
(`etc/gen-init.py --check` would differ): its axioms `opaqueInitsOk` (with `defaultRegistry.init`) and
`initFuncsOk` (`init.«0»`, unfolded by `prometheus.Assumptions` to the glue's `init.«0».impl`) now claim
triples of concrete code that resolves `promreg`'s names, for every semantics satisfying
`prometheus.Assumptions`, including one whose table maps `promreg.NewRegistry` to a panicking function.
Both must go (stage 4 replaces them by the proof), or the glue must not resolve names.

**Options (a decision for the user; the instruction is that no closed statement changes but for losing
`HNs`/`Ns`/`hNs`/`hNsIds`):**
1. **The closed theorems gain `[promreg_sem : promreg.Assumptions]`** (the semantics' function table holds
   the model's code: what the trusted model means; satisfiable, the names are the model's own package path),
   as `mvcc_sem`/`srv_sem`/`cache_sem` were added for packages main does not import. Every theorem between
   (prometheus's `Init`, the registering packages' `Init`/`InitLinked`, `MustRegister.wp_proof`, their
   `Link`s, the `PkgTable`s' sections) takes the instance: a `variable` in the generated files
   (`etc/gen-init.py`, `etc/gen-link.py`), the same ripple as `PromRegGS`'s (§"Handoff"), but of a `Prop`
   class, so no ghost-name question. A closed-statement change: needs the user's (and #15's) approval.
2. **No resolution of the model's names**: translate client_golang's prometheus with `sync` among its imports,
   and make the model's code the trusted bodies of client_golang's own names (`NewRegistry`,
   `(*Registry).Register`, `MustRegister`, `Register`, `init.0`; the builtin lists as literals in them), over
   client_golang's `Registry` struct if it translates with `sync` (its fields are `mtx`, `collectorsByID`,
   `descIDs`, `dimHashesByName`, …: the model's state). The model is then trusted Lean, not verified Go: the
   stage-3' proofs are redone over those names, and `model_test.go` stays the evidence. No closed statement
   changes.
3. **Ask Perennial/goose for a translation option** that adds an import edge (`extra_imports`: prometheus
   imports the model's package), so that `prometheus.Assumptions` gets `import_promreg_Assumption` and the
   package's `pkgImportedPkgs` gets `promreg` (then `define_is_pkg_init` and the package tables follow by
   themselves). A general translator feature (trusted code that calls another translated package), to be
   proposed on its own (`notes/perennial-changes.md`); no closed statement changes. Recommended.

Until decided, `PkgInit.lean` keeps its `True` fact and nothing above `Registry.lean` changes but what
`collectorName`'s definition rebuilds. Next once decided: `isPkgInit prometheus` (`∃ l γ, globalAddr
defaultRegistry ↦□ l ∗ localName promKey γ ∗ isRegistry γ descId l`, with `promreg`'s fact among its
dependencies), `MustRegister`/`Register`/the initializer as theorems (`localName_agree` for γ = γ′), then
`NewServerMetrics`' clause and `Register.spec`'s rights (which the `metricsP` lock of `v3rpc`'s
`getServerMetrics` must carry in its `nil` case, from `v3rpc`'s init resources: both collector IDs, with and
without the histogram, since the option is decided at run time), then stage 5.

## Stage 4 under option 1 (2026-11-22, the session after the user's decisions)

**The user's decisions** (kaashoek, 2026-11-22): (1) the blocker's option 1: every closed theorem that
reaches prometheus gains `[promreg_sem : promreg.Assumptions]`, so do the generated `Init`/`Link`s and the
generic start theorems between; the closed statements change only by that instance and by losing
`HNs`/`Ns`/`hNs`/`hNsIds` (listed in `notes/prom-registry-start-change.md`, for Upamanyu's sign-off, #15);
(2) zeldovich's constructor change is accepted (#15; #18's branch `prove-ps2-metrics/2026-11-22`):
`NewGauge`/`NewCounter`'s posts will carry `metric.isGauge`/`isCounter`, their `prometheus.toml` translates
seven methods and stops treating `Desc`, `Metric` and ~13 more types as opaque. Their constructors' method
clauses and `MetricRep.lean` are theirs; whichever branch lands second merges `prometheus.toml` (their
methods plus our `trusted = [...]`). Nothing here depends on `Desc` being opaque (`collectorDescs` reads a
collector, not a `*Desc`).

**Done** (commit `7d8792914e`, built against `manifest-ln14`):
* **The rights read the run's name themselves; the builtins take none** (`notes/decisions.md`, the entry of
  this date): `promreg.idTok k := ⌜k ∉ builtinKeys⌝ ∗ ∃ γ, localName regKey γ ∗ k ↪[γ] ()`, `regTok k :=
  ⌜k ∈ builtinKeys⌝ ∨ idTok k` in the registry invariant, `isRegistry f r` without `γ`, `SeedBuiltins`
  without rights, `promReg_alloc m (m !! regKey = none) ks` from `ownLocalNames m`. The three promreg proofs
  rebuilt (`regToks_insert_builtin`, `union_insert_r_same`). `prometheus.regFree n := ⌜n ∉ builtinNames⌝ ∗
  idTok (descId n)`; `promKey` gone (`promreg.regKey`); `prometheus.namesFree` is `regFree` of each name.
* **prometheus's fact and initializer**: `promInit := ∃ l, globalAddr defaultRegistry ↦□ l ∗ isRegistry
  descId l` (`PkgInit.lean`, hand-written `IsPkgInit`/`GetIsPkgInitWf` with dependencies `[time, promreg]`).
  `etc/gen-init.py`: `EXTRA_DEPS` (prometheus → promreg; inventory, `pkginfo_imports`, so the package tables),
  `INST_HAND`, prometheus's `SPECIAL` (the glue's `defaultRegistry.init` and `init.«0»` stepped over
  `NewRegistry`/`SeedBuiltins`), promreg's `Init.lean` generated, prometheus's split into
  `Init`/`InitLinked` (it applies the model's proofs), and `PROMREG_VAR` (`variable [promreg_sem : ...]`) in
  every init and package table whose closure has the model. **Retired**: prometheus's `initFuncsOk`
  (`init.«0»`) and `defaultRegistry.init` from its `opaqueInitsOk` (the soundness hazard of "Stage 4
  started" is gone for them).
* **`MustRegister.wp_proof` is a theorem** (callee: `promreg.Registry.Register.spec`), its spec taking
  `isPkgInit prometheus` and `regFree n`; the generated registering initializers apply
  `(MustRegister.wp_proof promreg.Registry.Register.wp_proof)` with `try iPkgInit`. The glue's names
  (`model.Collector`, `model.Register`, `model.defaultRegistry`) are rewritten to the translation's
  (`Registry.lean`, `model_*_eq`: `Collector.ty` is irreducible, so the instances do not see through).
  **Pitfall** (half a session): never let the kernel compare `(nameDesc n dh).ID'` with `descId n`, nor
  build `idToks (descKeys [nameDesc n dh])` inside a big proof: it unfolds `descId` (the xxhash) on a
  variable to the recursion limit ("(kernel) deep recursion" at the theorem, whatever `maxRecDepth`).
  `generalize` the descriptor and go through `wp_Register_single` (a one-descriptor `Register` triple taking
  `idTok d.ID'`), as `MustRegister.lean` does.
* The full regeneration (`etc/gen-init.py`, 59 files: the registering packages' steps, `promreg_sem`,
  prometheus's importers now importing its `InitLinked`, the package tables' rows for promreg, the
  grpc-prometheus provider's init split): commit `8743c629f9`. Built (3777 jobs): every registering package's
  `InitLinked`, the etcd/k8s/mvccfull/mvccrand/leaseexpiryN package tables, etcdstart's and the WAL tester's
  `InitLinked`; `etc/gen-init.py --check` and `etc/tier-check.py --check` pass. Nothing above them (the
  `Adequacy`/`Results` files, the closed theorems) was built: they still pass `startRights`' `nameFree`s.

**Next session, in order**: `prometheus.Register` (below), then stage 5 from `goose_adequacy_start`
(`ownLocalNames ∅` in its premise, the names dropped: the final commit), the closed proofs (`promReg_alloc`
with the program's names' IDs, decided distinct and non-builtin), `etc/gen-link.py` only where a `Link`
applies a theorem taking `promreg_sem` (today none: v3rpc's `Link` applies the `Register` axiom), stage 6.

**Not done (stage 4):**
* `prometheus.Register.wp_proof` (grpc-prometheus's server metrics, `getServerMetrics`) is still the axiom,
  now about the glue's concrete code (the same hazard as `opaqueInitsOk` had; flag). Plan: (a) grpc-prometheus
  `Defs`: the server metrics' names (`grpc_server_started_total`, `_handled_total`, `_msg_received_total`,
  `_msg_sent_total`, and with the histogram option `grpc_server_handling_seconds`, from the pinned
  go-grpc-middleware provider's `server_metrics.go`, to confirm) and `srvDescs hist dhs` (their
  `nameDesc`s in `Describe`'s order); (b) `NewServerMetrics`' post gains `⌜∃ hist dhs, collectorDescsAre (mkOk
  *ServerMetrics m) (srvDescs hist dhs)⌝` (statement otherwise unchanged; **flag it**, #24's area); (c)
  `v3rpc.metricsP`'s `nil` case holds `idToks grpcKeys` (the five IDs and both collector IDs, the XOR of four
  and of five: decided distinct and non-builtin by `decide +kernel`), and v3rpc's init resource gains them:
  `ownInitResL`'s entries are names (`regQs`), so either v3rpc's entry gets a keys component
  (`regResL` over `(q, names, keys)`) or the keys go in as pseudo-names; (d) `Register.spec` takes `isPkgInit
  prometheus`, the collector fact and `idToks (descKeys ds)`, proved like `MustRegister` (one `Register` of
  `ds`), and `getServerMetrics` splits `idToks grpcKeys` by the option.
* Stage 5 (the closed theorems) and 6 (gates, the full build, the TCB baseline) as planned above; the closed
  proofs no longer pass `startRights`' `nameFree`s to the root initializer (the types differ now: `namesFree`
  is `regFree`'s) but `promReg_alloc`'s rights, from `ownLocalNames ∅`, which only the start model's change
  gives: **if that change is dropped, the closed proofs have no way to make rights** (open decision).

## Stage 4 finished and stage 5 (2026-11-22, the session after "Stage 4 under option 1")

The coordinator's decisions (2026-11-22): the start model's change is required (its own commit; already in
the sign-off request on #15); the rights are to IDs, not names, so the registration rights get a keys
component (no pseudo-names); `NewServerMetrics` gains the descriptor clause (flagged); `prometheus.Register`
proved over the model.

**Done:**
* **`prometheus.Register` is a theorem** (`Proof/.../prometheus/Register.lean`, callee
  `promreg.Registry.Register.spec`; the axiom, which once the glue was in place claimed a triple of the
  glue's code for every semantics, is gone). Its spec is generic: a collector `c` describing `ds`
  (`collectorDescsAre`), `descsOk descId ds`, `isPkgInit prometheus ∗ idToks (descKeys ds)` ⊢ returns
  `nil`.
* **grpc-prometheus's server metrics** (`providers/prometheus/Defs.lean`): `srvNames hist` (the four
  counter vectors and, with the histogram, the histogram vector, in `Describe`'s order, from
  `server_metrics.go` of v1.1.0), `srvDescs hist dh` (their label-free `nameDesc`s, one dim hash per name),
  `srvKeys hist` (`descKeys` of them: `srvDescs_keys`), `grpcKeys` (`ids4 ++ [x4, id5, x5]`: the IDs of
  either choice; `srvKeys_false`/`_true` by `decide +kernel`), `grpcKeys_srv`. **Flag**:
  `NewServerMetrics.spec`'s post gains `⌜∃ dh, collectorDescsAre ⟨*ServerMetrics, #m⟩ (srvDescs
  (!os.isEmpty) dh)⌝` (its axiom's text unchanged; #24's area). No Go evidence yet for the provider (the
  model test checks client_golang's constructors only): a `TestServerMetricsDescs` beside
  `TestConstructorDescs` would need the provider in `examples/go.mod` (open).
* **`v3rpc.metricsP`**: `(⌜m = null⌝ ∗ idToks grpcKeys) ∨ (⌜m ≠ null⌝ ∗ promSrvMetrics m)`;
  `getServerMetrics` spends the rights on its one registration (its error branch is now dead).
* **The keys component** (`PkgInitRes.lean`): `regResL` over `(q, names, keys)`, entry resource
  `namesFree names ∗ idToks keys`; `prometheus.regsFree qs` the `wp_initialize'` precondition (was
  `namesFree initNames`; `initNames` gone); `regKeysOf`, `regQsOk` (decidable: IDs distinct, none a
  builtin's, no builtin name), `idToks_regsFree`, `regsFree_alloc`, **`wp_init_of_localNames`** (the
  initializer's triple from `ownInitializing ∗ ownLocalNames ∅`, given `regQsOk qs`). `etc/gen-init.py`:
  `REG_KEYS` (v3rpc: `grpcKeys`), a `regKeys` per `PRE_RES` package, the `_self` form splitting `HR` into
  `HR`/`HK`; v3rpc's lock gets `HK`.
* **`promreg_sem` in the Links** reaching `Register`'s proof: `etc/gen-link.py`'s `PROMREG_VAR` for
  `--v3rpc --common --cluster3 --linkv3p --linkvtxn --watchkv --authkv --cachekv --k8setcd3 --k8s
  --k8s-etcd3` (the modes that take `idIssueExt`, but `--server`), and the hand-written linking modules
  above them (see the commit).
* **Stage 5**: `Start.lean` (its own commit: names gone, `ownLocalNames ∅` in the WP premise), the generic
  etcdstart theorems (`progOk`'s initializer resource is `ownLocalNames ∅`; `Ns`, `HNs`, `hNs`, `hNsIds`
  gone), the closed proofs (`wp_init_of_localNames _ regQs (by decide +kernel)`), `prometheus.nameFree`,
  `descIdsDistinct`, `read.readRegPerm`, `namesUnclaimed`/`nameUnclaimed` deleted, the TopLevelDefs'
  metric-name lists deleted. The exact list of changed closed statements: `notes/prom-registry-start-change.md`.

**Status of the above (2026-11-22, WIP milestone):** committed and pushed as work in progress, not built through
(a full build against `manifest-ln14` was running with no failure up to job 14617/17938 when this was
committed). **Superseded in part the same day**: Upamanyu rejected perennial#681 (`ownLocalNames`/`localName`)
on #15; the start model's change must be removal only, and the registry's ghost name must reach
prometheus's package fact through untrusted proof code ("Option 4" below). What survives: `Register` proved
over the model, the keys component (`regsFree`, `REG_KEYS`), `NewServerMetrics`' clause, `metricsP`'s rights,
`promreg_sem` in the Links and the closed theorems. What goes: `ownLocalNames ∅` in `goose_adequacy_start`
and in the generic theorems' `progOk`, `wp_init_of_localNames`/`regsFree_alloc` over it, and `idTok`'s
`localName`.

## Option 4 (Upamanyu, 2026-11-22): the run's ghost name through untrusted proof code

**The decision** (Upamanyu on #15 and perennial#681, relayed by the coordinator): #681 is rejected; the
trusted adequacy statements gain nothing, and `Start.lean`'s change is removal only (`nameFree` out of
`startRights`; `Ns`, `hNs`, `hNsFree`, `hNsIds`, `nameUnclaimed`, `namesUnclaimed` deleted). The program's
proof allocates the registry's ghost state itself, inside each run's `Hwp` update (a crashed generation's
rights are over its own, stale, name); prometheus's package fact gets the name through untrusted proof code
(an instance or a package-level parameter); if `define_is_pkg_init` copying the instance into every
importer's fact is the obstacle, fix that machinery in Perennial (untrusted). `[promreg.Assumptions]` on the
closed theorems is fine.

**What spreads today, read at `/shared/perennial-c14cca87a` (`Perennial/Golang/Theory/Pkg.lean`).**
`define_is_pkg_init P` elaborates `IsPkgInit.mk deps P` with `deps := isPkgInit d₁ ∗ … ∗ True` over
`pkgImportedPkgs`, each `isPkgInit dᵢ` at the instance `synthInstance (IsPkgInit PROP dᵢ)` finds *in the
importer's context*. So if prometheus's instance is `instance [PromRegGS GF] : IsPkgInit (IProp GF)
prometheus`, every importer's `define_is_pkg_init` fails unless `[PromRegGS GF]` is in scope, and then its
own instance takes the argument, and so on up (52 packages; every module that elaborates their
`isPkgInit`, 2073). `build_get_is_pkg_init_wf` likewise synthesizes each dependency's `GetIsPkgInitWf`.
`solve_pkg_init`/`iPkgInit` (`pkgInitChain`) find a target `isPkgInit d` by `isDefEq` against
hypotheses, descending through `isPkgInit` (its `deps` field), `∗` and `□`; `is_pkg_init_finish` proves an
initializer's post by `isPkgInit_unfold` then `iframe #`.

**The design: a parametric package fact, existential in its importers' facts.**
1. *Perennial* (`Pkg.lean`, untrusted), new class: a package whose fact takes a parameter.
   ```lean
   class IsPkgInitParam (PROP : Type _) [BI PROP] (pkg_name : GoString) where
     Param : Type
     inst : Param → IsPkgInit PROP pkg_name
   /-- the fact of `pkg_name` at some parameter: what an importer knows of it -/
   def isPkgInitSome (pkg_name) [IsPkgInitParam PROP pkg_name] : PROP :=
     iprop(∃ x : IsPkgInitParam.Param PROP pkg_name, @isPkgInit PROP _ pkg_name (IsPkgInitParam.inst x))
   ```
   (`isPkgInitSome` persistent.)
2. *Perennial*, `define_is_pkg_init`: for each dependency `d`, if `synthInstance (IsPkgInit PROP d)`
   fails and `synthInstance (IsPkgInitParam PROP d)` succeeds, the conjunct is `isPkgInitSome d` instead
   of `isPkgInit d`. An importer's instance then needs no parameter: **no spread through `IsPkgInit`**.
3. *Perennial*, `build_get_is_pkg_init_wf`: unchanged. A parametric package's `GetIsPkgInitWf` instance
   takes the parameter (`g d = isPkgInit (inst x) d` at the `x` in scope), so an importer's
   `GetIsPkgInitWf` instance takes it too: the parameter spreads through the **well-formedness instances
   only** (declared once per package, by an explicit binder `instance [PromRegGS GF] : GetIsPkgInitWf …`,
   not a section variable, or the `IsPkgInit` instance beside it would take it too), and through their users:
   the generated `Init`/`InitLinked`/`PkgTable`s and the closed proofs. This is wanted: the wf instance is
   what pins the run's name for the initializers (below).
4. *Perennial*, tactics: `pkgInitChain` treats `isPkgInitSome d` as an atom (a target `isPkgInitSome d` is
   found by `isDefEq`, as today), and may descend through it to targets below `d` by `exist_elim` (the chain
   from `isPkgInit (inst x) d` to a target not mentioning `x` is built under a binder `x`). `is_pkg_init_finish`
   proves an `isPkgInitSome d` conjunct of the goal from `isPkgInit (inst x) d` in the context (`iexists _;
   iframe`, or a `Frame` instance for `isPkgInitSome`). Nothing else changes; no adequacy statement changes.

**In this repository** (after a pin bump bringing 1–4):
* `PromRegGS GF` (a class holding `γ : GName`) returns; `instance : IsPkgInitParam (IProp GF) prometheus :=
  ⟨PromRegGS GF, fun x => ⟨deps, promInit x.γ⟩⟩` (hand-written, with its deps `time`, `promreg`), and a local
  instance `[PromRegGS GF] → IsPkgInit (IProp GF) prometheus` for code at a known name.
  `promInit γ := ∃ l, globalAddr defaultRegistry ↦□ l ∗ isRegistry γ descId l`; `idTok γ k := ⌜k ∉
  builtinKeys⌝ ∗ k ↪[γ] ()` (stage 3''s form; `localName`/`regKey` go).
* **Where the name is known, and why it agrees.** (a) A registering package's initializer (`MustRegister` in
  `init()`): its generated `wp_initialize'_res` is in a section with `[PromRegGS GF]`; its rights are
  `regsFree` at that instance, and prometheus's fact comes from `prometheus.wp_initialize'` at the same
  instance, whose `Hinit` (the wf instance at that instance) says `g prometheus = isPkgInit (inst γ)
  prometheus`: whether prometheus's initializer runs now or ran before, the fact returned is at `γ`.
  (b) A run-time registration (`getServerMetrics`): the fact and the rights are stored together, packed:
  `metricsP`'s `nil` case holds `∃ x : PromRegGS GF, isPkgInit (inst x) prometheus ∗ idToks x.γ grpcKeys`
  (v3rpc's initializer, at the section's instance, has both), so v3rpc's own fact mentions no parameter.
  (c) Code that needs prometheus initialized but not the registry (the vectors' `WithLabelValues`, `With`,
  the server's paths that use metrics: 6 specs and ~7 proofs name `isPkgInit prometheus` today) takes
  `isPkgInitSome prometheus`, which `iPkgInit` finds in its package's deps.
* **The closed proofs** use the `_alloc` adequacy forms (`etcd_adequate_alloc`, as the k8s compactor
  registry's): `T γ := idToks γ (regKeysOf regQs)` allocated by `ghost_map_alloc` inside `Hwp`, then
  `letI : PromRegGS GF := ⟨γ⟩` and the program's `getIsPkgInit_wf` at it; `regQsOk regQs` decided by the
  kernel as now (but see "kernel" below). The WAL tester's crash proof does the same in each generation's
  `Hwp` (each generation allocates a new `γ`; a carried-over right is at the crashed `γ`, which no spec of the
  new generation takes). The generic etcdstart theorems keep `progOk`'s `R` (`regsFree` at the instance,
  through `T`); `goose_adequacy_start` is removal only.
* Unchanged from the WIP: the model and its proofs (with `γ` explicit), the glue, `Register` proved,
  `NewServerMetrics`' clause, the keys component, `promreg_sem` in the Links and closed theorems.

**Cost.** Perennial: one class, one definition, ~15 lines in `define_is_pkg_init`, the tactic support.
Here: the 52 importers' `GetIsPkgInitWf` instances get an explicit `[PromRegGS GF]` binder (a script;
`etc/gen-init.py` already lists them), the generated init/table files the variable (`PROMREG_VAR`'s
successor), the closed proofs `letI`; ~13 files move from `isPkgInit prometheus` to `isPkgInitSome`.
**Not avoided**: the wf spread (point 3) is inherent: an initializer that registers must know prometheus's
fact at its rights' name, and the only route from the run's start to the initializer is the
well-formedness of `get_is_pkg_init` (or the resources of `ownInitResL`, which are allocated before
prometheus's location exists).

**Rejected variants.** An existential parameter in the wf too (`∃ x, GetIsPkgInitProp (inst x) d g`): the
initializer learns some `x` and holds rights at the section's `γ`, with nothing equating them. A
sigma-packed `IsPkgInit` instance whose `isPkgInitDef` is `∃ γ, promInit γ` (no Perennial change): the
same lack of agreement for the initializers (Step A). The fact keyed by another package (`promreg`):
`promreg` is initialized before the registry exists.

**Kernel.** The WIP's `mvccrand` closed proof hit the default heartbeats deciding `regQsOk regQs` by
`decide +kernel` at the theorem (job 14620 of the full build): split it out as its own lemma with raised
`maxHeartbeats`, or decide `regKeysOf` once into a literal list first.

## Why the real client_golang registry is not translated (for Upamanyu's sign-off)

Read at client_golang v1.24.1 (`prometheus/registry.go`, `desc.go`, `go_collector_latest.go`,
`internal/go_collector_options.go`), common v0.70.1 (`model/metric.go`):
* **`Registry.Register` itself is translatable**: a `sync.RWMutex`, three maps (`collectorsByID
  map[uint64]Collector`), a goroutine running `c.Describe(descChan)` and closing a buffered channel, a
  `for range` drain in a `defer`, xxhash (already translated here). What goose or Perennial lacks is on its
  error paths only: `fmt.Errorf("… %s …: %w", desc, …)` (a `Stringer` and `%w`; `Desc.String` uses
  `fmt.Sprintf` with `%q` and `%v`) and the type switch on `*wrappingCollector`. Those paths are
  unreachable under the rights, so they **could be left stuck** (not modeled): the proof shows they are not
  reached.
* **`Desc`/`NewDesc`**: `constLabelPairs []*dto.LabelPair` (client_model's protobuf messages, protobuf-go's
  `protoimpl` runtime), `proto.String`, `sort.Sort(internal.LabelPairSorter)`, `model.IsValidMetricName`
  (with the default UTF-8 scheme a `utf8.ValidString`, no regexp at call time). Translatable with the
  protobuf types names-only (#18 is translating `Desc`'s methods), not stuck.
* **The obstacle is `init()`**, which every program runs: `MustRegister(NewProcessCollector(…))` and
  `MustRegister(NewGoCollector())`. `NewGoCollector` filters `runtime/metrics.All()` (the Go runtime's
  metric list, which depends on the toolchain version) through `regexp.Regexp.MatchString` with
  `internal.GoCollectorDefaultRuntimeMetrics = regexp.MustCompile(…)` (a package variable), calls
  `metrics.Read` for the histograms' buckets, and builds descriptors from the runtime's descriptions with
  string rewriting (`internal.RuntimeMetricsToProm`). common's `model.MetricNameRE = regexp.MustCompile(…)`
  is also compiled at initialization. None of this can be left stuck: a stuck initializer makes every
  program stuck. It needs either a regexp model and a trusted `runtime/metrics.All()` (whose content is the
  toolchain's, so trusted anyway), or a trusted summary of what `init()` registers: the model's
  `SeedBuiltins`, the 38 descriptor IDs and 2 collector IDs of configuration C, checked by `TestBuiltins`.
  (No `reflect` and no `sync.Map` on these paths; `procfs` is only read at `Collect`.)
* So a middle route exists: translate `registry.go`'s `NewRegistry`/`Register`/`MustRegister` and `desc.go`
  with their bodies (error paths stuck), keep `init()` trusted as `SeedBuiltins` is now, and the two regexp
  package variables as untranslated initializers (`opaqueInitsOk`: they return without panicking). The
  trusted part would shrink to `init()`'s registrations; the cost is a proof of the real `Register`
  (goroutine and channel included) instead of the model's, and `Desc` as a translated type (#18's area).

## Route (b) (2026-11-22): the real client_golang registry, `init()` the one trusted declaration

**The decisions** (Upamanyu and kaashoek on #15, 2026-11-22): (b) translate client_golang v1.24.1's real
`registry.go`/`desc.go` with their bodies, the untranslatable error paths left stuck; prometheus's `init()` the
only trusted code (a `TrustedCode` replacement over the translated registry, the built-ins' 38 + 2 IDs as
constants re-checked by a Go test on the pinned toolchain); the Go model retired (`examples/lib/promreg`, its
proofs, the glue, `[promreg.Assumptions]`); `Gather`/`Collect` not translated; Option 4 (`IsPkgInitParam`/
`isPkgInitSome`, untrusted Perennial machinery: another session, branch `pkg-init-param`); the closed proofs
allocate the registry's ghost name inside their `Hwp` (`etcd_adequate_alloc` forms); `Start.lean` changes by
removal only (no `ownLocalNames`). Kept from route (a), to be redone over the real registry: the ID-keyed rights
(the keys component, `grpcKeys`, `v3rpc.metricsP` holding them), `NewServerMetrics`' descriptor clause, the
deletion of `nameFree`/`namesUnclaimed`/`descIdsDistinct`/`readRegPerm`, §5's residue list.

### Step 1 (done, commits `c7a5cf7876`..`8168da033b`)

* **The branch was reset to `lean`'s code** (merge `c7a5cf7876`, then `lean`'s tree but for the notes): the
  model, the glue, the `ownLocalNames` forms and every closed proof over them are gone from the tree (they stay
  in the history: `249c42aa98`). `lean` had moved its Perennial pin to `101637598` (from `c14cca87a`), so the
  branch builds against **`/shared/tmp/manifest-1016.json`** (a worktree `/shared/perennial-101637598`, made by
  this session from `/shared/perennial-c14cca87a`'s repository, its `.lake` copied).
* **Translation** (`Code/github_com/prometheus/client_golang/prometheus.toml`): `NewRegistry`, `(*Registry).Register`,
  `(*Registry).MustRegister`, `Register`, `MustRegister`, `defaultRegistry`/`DefaultRegisterer`/
  `DefaultGatherer` (their initializers), `capMetricChan`/`capDescChan`, `AlreadyRegisteredError.Error`,
  `NewInvalidDesc`, `Desc.Err`; `Desc` and `Registry` are structs now. Imports `sync`, `fmt` and client_model's
  `dto` (a new package of the etcd project, types and names only, `Code/github_com/prometheus/client_model/go.toml`;
  its fact `True`, `Proof/github_com/prometheus/client_model/go/PkgInit.lean`; its generated `Init.lean` has the
  usual trust-boundary axioms of a names-only protobuf package, `opaqueInitsOk` of its variables, `MetricType_name`,
  `MetricType_value`, the file descriptor's, and `initFuncsOk` of its `init()`: Go runs them, since prometheus
  imports `dto`; they are new axioms of the trust base, the price of `Desc` as a struct). `Register`'s error paths translate (goose now translates the type switch, `TypeAssert2`) but call
  names-only functions (`fmt.Errorf` is Perennial's trusted model; `Desc.String` and
  `wrappingCollector.unwrapRecursively` have no body), so a run reaching them is stuck. **Not translated**:
  `NewDesc`, `V2.NewDesc`, `Desc.String`, `WithUnit` (they would import common/model, prometheus/internal and
  xxhash, whose package variables compile regexps: more untranslated initializers in the trust base, for code
  no verified program reaches: an open point for the sign-off), `Unregister`, `Gather`, `Collect`, `Describe`.
* **The trusted `init()`** (`TrustedCode/github_com/prometheus/client_golang/prometheus.lean`): with `r :=
  defaultRegistry` (already `NewRegistry()`), `seed.insertAll` of the built-in descriptor IDs into
  `r.descIDs` (`struct{}{}`), of the names with their dim hashes into `r.dimHashesByName`, and of the two
  collector IDs into `r.collectorsByID` (the nil `Collector` as value: a documented deviation, read only on
  `Register`'s `AlreadyRegisteredError` path, `Unregister` and `Gather`). Constants `seed.descIDs`, `seed.dims`,
  `seed.collectorIDs`; `examples/lib/prombuiltins/seed_test.go` (`TestSeedConstants`) parses them from the Lean
  file and compares with the real default registry (and a new registry with the two collectors registered) on
  `go1.27.3`, linux/amd64, client_golang v1.24.1 (it checks all three): `cd examples && GOTOOLCHAIN=go1.27.3 go
  test ./lib/prombuiltins/` passes, and fails when a constant is changed.
* **prometheus's initializer proved** (`etc/gen-init.py` `SPECIAL[prometheus]`): the three translated variable
  initializers stepped (`NewRegistry`'s body inline: `wp_map_make1` thrice), the trusted `init.«0»` through
  `EtcdGrove.prometheus.wp_seed_insertAll` (`Proof/.../prometheus/Seed.lean`, by induction on the list; with
  `seed_Registry_eq`/`seed_Collector_eq`/`seed_defaultRegistry_eq`, the trusted file's literal names equal to
  the translation's). **Axioms removed**: `initFuncsOk` (prometheus's `init.«0»`), and `defaultRegistry.init`,
  `DefaultRegisterer.init`, `DefaultGatherer.init` out of `opaqueInitsOk`. **Added**: client_model `dto`'s
  `opaqueInitsOk` and `initFuncsOk` (above). The fact is still
  `True` (the maps are dropped at the end); step 2 makes it the registry.
* **Hazard until step 2** (as route (a)'s glue had): `MustRegister.wp_proof` and `Register.wp_proof` are still
  the trust-boundary axioms, and `MustRegister`/`Register` now have bodies (`prometheus.Assumptions` unfolds
  them), so the axioms now claim triples of the real code; they are what step 2 proves.

### Step 2 (not started: the design, for the next session)

1. **The collector fact becomes a persistent `IProp`** (the one statement change to the constructors' specs, a
   flag for #18): `Register` reads each `*Desc` its collector's `Describe` sends, so whoever states what a
   collector describes must give the descriptors' points-to's, which a pure `Prop` cannot (a `⊢ p ↦□ d` is false;
   a `Prop` that claims it makes the constructor axioms inconsistent). So `collectorName c n : IProp GF` :=
   `∃ p d, p ↦□ d ∗ ⌜d.fqName' = n ∧ d.id' = descId n ∧ d.err' = interface.nil⌝ ∗ describes c [p]`, and the
   constructors' posts `⌜collectorName c n⌝` become `collectorName c n` (`NewCounter`, `NewCounterVec`,
   `NewGauge`, `NewGaugeFunc`, `NewGaugeVec`, `NewHistogram`, `NewHistogramVec`; 13 files name it), `MustRegister.spec`
   takes it in its precondition. `describes c ps` (persistent): for every SPSC channel (Perennial's
   `Chan/Idioms/Spsc.lean`: `isSpsc γ ch P R`, `spscProducer γ sent`), `[∗ list] i ↦ p ∈ ps, P (len sent + i) p -∗
   WP (MethodResolve Collector.ty "Describe" #c) #ch {{ v, ⌜v = #()⌝ ∗ spscProducer γ (sent ++ ps) }}` (the
   method call as `Register`'s goroutine makes it: the channel converted to send-only, the same location).
   grpc-prometheus: `NewServerMetrics`' post gains `describes ⟨*ServerMetrics, m⟩ ps` of the server metrics'
   descriptors (`srvDescs hist`: route (a)'s `providers/prometheus/Defs.lean`, `249c42aa98`).
2. **The registry** (prometheus `Registry.lean`, defs): `idTok γ k := ⌜k ∉ builtinKeys⌝ ∗ k ↪[γ] ()` with
   `builtinKeys := seed.descIDs ++ seed.collectorIDs`, `builtinNames := seed.dims.map (·.1)` (the trusted file's
   constants, not copies); `regInv γ r` (the RWMutex's guarded resource at fraction 1): the maps `D N C` at the
   field pointers (`ownMap`), `r.uncheckedCollectors` and its slice, the element `k ↪[γ] ()` of every registered
   non-builtin descriptor ID and collector ID, and `∀ n ∈ dom N, n ∈ builtinNames ∨ descId n ∈ dom D`, builtin
   keys and names registered; `isRegistry γ r` (persistent): the field pointers (read-only after `NewRegistry`)
   and `isRWMutexGuard r.mtx (regInv γ r)` (Perennial `sync/RWMutexGuard.lean`: a writer needs only the guard).
   prometheus's fact `promInit γ := ∃ r, globalAddr defaultRegistry ↦□ r ∗ globalAddr DefaultRegisterer ↦□
   (interface of *Registry r) ∗ isRegistry γ r` (the gen-init steps above keep the maps instead of dropping them,
   and allocate the guard after `init.«0»`).
3. **`(*Registry).Register`'s proof** (the bulk): `make(chan *Desc, 10)` then `start_spsc` with `P i p := ⌜ps !! i =
   some p⌝`, `R l := ⌜l = ps⌝`; the goroutine (`wp_fork`, no thread token needed) runs `describes` and
   `wp_spsc_close`; `Lock` by the guard; the `chan.forRange` loop (`pure_wp_chan_for_range`, `wp_spsc_receive`)
   with the pure loop state of route (a)'s `Registry__Register.lean` (`249c42aa98`: the prefix's IDs, their XOR,
   the names seen); the tokens give each `desc.id ∉ dom D` (`idTok` against the invariant's element), the
   collector ID's absence, and the names' absence (the invariant's name clause and `n ∉ builtinNames`); the
   inserts, then the tokens go into the invariant; the deferred drain (the channel is closed and drained: the
   loop ends on `ok = false`) and `Unlock`. Spec: `{{ isRegistry γ r ∗ describes c ps ∗ descs ps ds ∗ idToks γ
   (descKeys ds) ∗ ⌜descsOk ds⌝ }} r.Register(c) {{ RET nil }}`. `MustRegister`: the loop over the slice, then
   `prometheus.MustRegister`/`Register` through `DefaultRegisterer`'s interface (from the fact).
   **Kernel pitfall** (route (a), "Stage 4 under option 1"): never let the kernel compare `(nameDesc n dh).ID'`
   with `descId n` or build `idToks (descKeys …)` of a literal inside a big proof; `generalize` and go through a
   one-descriptor lemma.
4. **Option 4** once Perennial's `IsPkgInitParam` is available: `class PromRegGS (GF) where γ : GName`;
   `instance : IsPkgInitParam (IProp GF) prometheus := ⟨PromRegGS GF, fun x => ⟨deps, promInit x.γ⟩⟩` (and the
   local `[PromRegGS GF] → IsPkgInit` instance); `etc/gen-init.py`: `INST_HAND` for prometheus, the importers'
   `GetIsPkgInitWf` instances with an explicit `[PromRegGS GF]` binder, the init and table files' variable; ~13
   files from `isPkgInit prometheus` to `isPkgInitSome`. The keys component of the rights (route (a)'s
   `PkgInitRes.lean`: `regResL` over `(q, names, keys)`, `regsFree`, `regKeysOf`, `regQsOk`, `REG_KEYS`) with `idTok
   γ` at the instance's `γ`; `v3rpc.metricsP`'s `nil` case packs `∃ x : PromRegGS GF, isPkgInit (inst x)
   prometheus ∗ idToks x.γ grpcKeys`.
5. **The closed proofs** (`etcd_adequate_alloc` forms): in `Hwp`, `ghost_map_alloc` of `regKeysOf regQs` (decide
   `regQsOk` once into a lemma with raised heartbeats: route (a)'s mvccrand hit the default), `letI : PromRegGS
   GF := ⟨γ⟩`, the program's `getIsPkgInit_wf` at it; the WAL tester's crash proof the same per generation.
   Then **`Start.lean`, removal only** (`nameFree` out of `startRights`, `Ns`/`hNs`/`hNsFree`/`hNsIds`,
   `nameUnclaimed`/`namesUnclaimed` deleted), `descIdsDistinct`, `read.readRegPerm`, `nameFree`, the TopLevelDefs'
   name lists; `notes/prom-registry-start-change.md` rewritten as the final trusted diff.

**Blocked on the Perennial pin** (an open decision for the coordinator): the plan's
`/shared/perennial-pkg-init-param-c14` (manifest `/shared/tmp/manifest-pip14.json`) is to be on `c14cca87a`, but
`lean` (merged here) pins Perennial `101637598`; Lean's translations of `101637598`'s goose do not build on
`c14cca87a` (326 files differ). The branch needs `pkg-init-param` on `101637598` (or on Perennial's `lean`, with a
pin bump), as a manifest like `manifest-1016.json`. (`/shared/perennial-pkg-init-param` itself is on Perennial
`lean`'s `74471ecd8`, a descendant of `101637598`.) **Resolved** (the coordinator, 2026-11-22): Option 4 is being
cherry-picked onto `101637598`; step 2 builds against `/shared/tmp/manifest-pip1016.json` once it exists.

**Sign-off points** (`notes/prom-registry-start-change.md`, the draft of the final trusted diff, part 1): the `dto`
initializer axioms that come with `Desc` as a struct, and `NewDesc` left untranslated.

### Step 2, milestone 2 (2026-11-22): Option 4 for prometheus, the package side

Built against `/shared/tmp/manifest-pip1016.json` (Perennial `101637598` plus Option 4, `6d0c4f8dc`).
* **`collectorName` is a definition** (`RegInv.lean`, persistent `IProp`: a descriptor pointer `p ↦□ d`, `d`
  named `n`, ID `descId n`, valid, and `describes c [p]`); the axiom in `Registry.lean` is deleted. The seven
  constructor specs' posts changed only from `⌜collectorName c n⌝` to `collectorName c n` (and `NewGaugeFunc`'s
  `⌜nameOk → collectorName⌝` to `(⌜nameOk⌝ → collectorName)`), plus an import of `RegInv` (a flag for #18).
* **Option 4** (`PkgInit.lean`): `class PromRegGS (GF) where γ : GName` (`EtcdGrove.prometheus`, `RegInv.lean`);
  `promInit γ := ∃ r, globalAddr defaultRegistry ↦□ r ∗ globalAddr DefaultRegisterer ↦□ interface.mkOk
  (*Registry) #r ∗ isRegistry γ r`; `IsPkgInitParam` instance (`Param := PromRegGS GF`), the local
  `isPkgInit_inst [x : PromRegGS GF]`, `get_isPkgInit_wf_inst [PromRegGS GF]`. The 53 importers' hand-written
  `GetIsPkgInitWf` instances (46 files, WalTester's tester included) take `[EtcdGrove.prometheus.PromRegGS GF]`;
  the generated Init/InitLinked/PkgTable files a section variable `promreg_gs` (`SPECIAL[prometheus]`'s
  `vars`/`table_vars`). Code needing prometheus initialized only (the vectors' specs, the server's six proofs)
  names `isPkgInitSome`. `isRegistry`/`idTok` are generic in `HasLC` (importers' facts are).
* **Rights keyed by ID** (`PkgInitRes.lean`): `regRes (q, Ns, Ks) := idToks γ (Ns.map descId ++ Ks)` at
  `PromRegGS.γ`, `regsFree`, `regResL`, `regKeysOf`, `regQsOk` (IDs nodup, none built-in, no built-in name),
  `idToks_regsFree`. `namesFree`/`nameFree`/`namesUnclaimed`/`descIdsDistinct`/`readRegPerm` are still there
  (Start.lean, the closed proofs, `read/Metrics.lean`), for the next milestone to delete.
* **`prometheus.MustRegister`/`Register` are theorems** (over `(*Registry).MustRegister`/`Register`'s specs);
  their specs quantify `∀ [promreg_gs : PromRegGS GF]`. **Axioms removed**: `collectorName`,
  `prometheus.MustRegister.wp_proof`, `prometheus.Register.wp_proof`. **Axiom changed**:
  `grpc_prometheus.NewServerMetrics.wp_proof`, whose post gains `∃ ps ds, describes ⟨*ServerMetrics, m⟩ ps ∗
  ps ↦□ ds ∗ ⌜srvDescsOk (!os.isEmpty) ds⌝` (true of providers/prometheus v1.1.0's `Describe`; the names, IDs
  and validity only). `v3rpc.metricsP`'s `nil` case holds `∃ x : PromRegGS GF, isPkgInit (inst x) prometheus ∗
  idToks x.γ grpcKeys`; `getServerMetrics` registers with them.
* **gen-init**: prometheus's initializer keeps the maps, splits the `Registry`, `isRegistry_init` at the
  instance's `γ`, fact `promInit γ` (`INST_HAND`); the registering packages take `idToks γ [descId n]` per
  registration (`idToks_names_cons`) and call `MustRegister.wp_proof (Registry.MustRegister.wp_proof
  Registry.Register.wp_proof)`; `REG_KEYS` (v3rpc: `grpcKeys`, stored in `metricsP`).

### Step 2, milestone 3 (2026-11-23): the closed proofs allocate the rights; `Start.lean`'s names part removed

Built against `/shared/tmp/manifest-1a03.json` (Perennial `1a0322fc6`, lean's pin at `aa1eb4da33`, which has
Option 4 as perennial#684).
* **Merges.** `lean` at `aa1eb4da33` (14 conflicts: generated files and baselines from lean's side, regenerated
  with `etc/goose.py --project etcd` and `etc/gen-init.py`; `gen-init.py` and `decisions.md` both sides). lean's #23
  replaced `opaqueInitsOk` by goose `[[skip]]` entries; `defaultRegistry`, `DefaultRegisterer`, `DefaultGatherer`
  are taken off prometheus's skip list (this branch translates their initializers), the other skips kept.
  `dto`'s variables are not skipped (its `opaqueInitsOk` stays; skipping them is a possible follow-up). Then
  **`net-swap` as a branch** (not in `lean` yet): first `df4369bae2`, then its newer tip `a711639023`; its side
  for what it retires (`etcd/all`, `k8s/all`, `leaseexpiryN`'s closed theorems, Start.lean's address part).
* **net-swap follow-up**: its tip did not build: 34 hand-written linked results reaching `net.Listen` lacked the
  `[_root_.Perennial.net.FieldAssumptions]` binder its own rule gives them (`restart`, `restartN`, `putget*`,
  `lease*`, `auth*`, `compact*`, `txnlinfaultsN`, `etcd/all`'s and `k8s/*`'s `MainLinked`/`Results`); added
  here, the same edit net-swap's session will make (no other change to them).
* **Other net-swap follow-ups** (its tip fails these checks too): `etc/api/etcdstart.txt` listed the deleted
  `AdequacyMembers`; and `etc/proof_roots.py` grouped `Net/` roots that reach the main tree's
  `Code.net.textproto` with ones that reach `Net.Code.net.textproto` (the same names) into one Lean run of
  `etc/tcb-report.py`, which could not load ("environment already contains ..."): `shadows_part` now keys a run
  also by the main-tree translations a part translates too. `etc/ModelParamCheck.lean` (gates' model-param) had
  the same clash and passes with it too.
* **Gates**: `etc/gates.sh` (`LAKE_PACKAGES=/shared/tmp/manifest-1a03.json`, `PERENNIAL_DIR=/shared/perennial-1a0322fc6`,
  `GATES_FAILFAST=0`) all passed at `569d24e638` plus this note (build 24784 jobs, tcb 376 axioms 0 sorries, 51
  collections, goose, gen-init, tier, interfaces, model-param, axiom-tok).
* **`Start.lean`, removal only**: `prometheus.nameFree` out of `startRights`; `Ns`/`hNs`/`hNsFree` out of
  `goose_adequacy_start` and `goose_adequacy_start_all`, and `hNsIds` out of the latter; the axiom
  `prometheus.nameUnclaimed` and `prometheus.namesUnclaimed` deleted. Then dead and deleted: the axiom
  `prometheus.nameFree` (`Registry.lean`), `prometheus.namesFree` (`PkgInitRes.lean`), `descIdsDistinct`,
  `read.readRegPerm`, `mvccrandNames`, `mvccfullMetricNames`, the etcd/dist draft's `serverNames`/`clientNames`.
* **The closed proofs** (mvccrand, mvccfull): in `Hwp`, `prometheus.regKeys_alloc` (`PkgInitRes.lean`: a fresh
  ghost map with the elements of `regKeysOf regQs`, from `regQsOk regQs`), `letI : PromRegGS GF := ⟨γreg⟩`,
  `idToks_regsFree`, then the program's `wp_initialize'` at it. `regQsOk` is decided once per program,
  `<ex>_regQsOk`, through `regQsOk_of_keys` over the IDs as literals (`<ex>RegKeys`, computed with
  cespare/xxhash and checked by the kernel): deciding `regQsOk` directly made the kernel rehash the names for
  every pair `Nodup` compares (21 GB before it was stopped), and `∀ k ∈ L, k ∉ builtinKeys` timed out in the
  elaborator's `whnf` (`(L ++ builtinKeys).Nodup` does not). The WAL tester has no closed adequacy theorem over
  its initializer (`tester_crash` runs none), so nothing to allocate there; the generic etcdstart theorems that
  survive net-swap take no names.
* **Statements**: each closed statement loses only `HNs` (`notes/prom-registry-start-change.md`, part 5).
* **Trust base** (`etc/tcb-report.py --check --update`; collections `mvccfull`, `v3rpc`, and net-swap's
  `client`, `cache-client` updated): this branch's changes are `prometheus.nameFree`, `nameUnclaimed`,
  `collectorName`, `MustRegister.wp_proof`, `Register.wp_proof`, prometheus's `initFuncsOk` gone, client_model
  `dto`'s `initFuncsOk`/`opaqueInitsOk` new (`notes/prom-registry-start-change.md`, part 3, which also lists the
  baseline's net-swap changes). Interfaces of `backend`, `etcdstart`, `mvcc` regenerated (their
  `wp_initialize'` take `regsFree regQs` at `[PromRegGS GF]`, milestone 2).
* **Pending**: `lean` has since moved to Perennial `9c3b81f30` (`82950b71a3`, manifest
  `/shared/tmp/manifest-9c3b.json`), and `net-swap` has merged it (`876c4a595a`); merging them here (conflicts
  expected in the package-init proofs: lean's side) is the next step. Then sign-off (#15) and landing (after
  net-swap lands).

### On `lean` after net-swap landed (2026-11-23)

Merged `lean` at `82847d941b` (net-swap landed; Perennial `70706ce5e`, manifest `/shared/tmp/manifest-7070.json`).
* **Conflicts**: `prometheus.toml` (both: our registry's translate list plus #35's/prove-ps2-metrics' `gauge`
  methods and `ExponentialBuckets`, the union of the imports); client_model `dto` (lean's side: lean now imports it
  for the metrics' `labelPairs`, with its variables skipped and its `init()` a trusted no-op model, so its
  `opaqueInitsOk`/`initFuncsOk`, which step 1 had added, are gone); `NewGauge.spec` (lean's `isGauge` with our
  `IProp` `collectorName`); `apply/Base.lean` (lean's `capInit` fact, our `[PromRegGS GF]` binder);
  `etc/proof_roots.py` (lean's `shared_net`, which supersedes this branch's `shadows_part`); `etc/gen-init.py` (the
  registration patterns also over lean's `⟨#R…, -⟩` gauges); generated files, baselines and the mvcc* Adequacy
  docstrings (lean's side, then regenerated). net-swap's content is lean's; this branch's earlier direct merges
  of it reconcile with no further change.
* **Follow-ups of the merge**: lean's new `gauge.{Set,Add,Sub,Inc,Dec}` specs and `MetricLaws` name prometheus's
  fact as `isPkgInit`; under Option 4 they take `isPkgInitSome` (as the vectors' specs), and so do
  `ReportEventReceived` and `RaftCluster.updateMembershipMetric`; the generated gauge steps close that premise by
  `iPkgInit`; mvcc's initializer (23 registrations over persistent `collectorName`s) gets `maxRecDepth 20000`.
* **#39** (the etcdserver `init.0` registrations as a `register(SPECIAL[etcdserver], …)` entry) is not on `lean`
  at `82847d941b`: nothing to port yet. When it lands, its entry goes through `register()`/`reg_steps` like the
  others (each registration takes `idToks γ [descId n]`, its `With(..).Set(1)` steps after).
