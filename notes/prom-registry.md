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
