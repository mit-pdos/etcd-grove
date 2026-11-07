# k8s's feature-package initializers (axiom review, 2026-11-07; sweep B1-4)

**Reviewed** (branch `sweep-atkC` at lean `ad87892323`):

- `k8s_io.apiserver.pkg.util.feature.DefaultFeatureGate_init`
  (`Proof/k8s_io/apiserver/pkg/util/feature/Init.lean:51-55`), whose postcondition becomes
  `featureInit` (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean:60-64`), the package's
  `isPkgInit` fact (`Base.lean:132-134`):

      ∃ g, globalAddr DefaultFeatureGate ↦□ GoInterface.ok g ∗
        □ ∀ (f : val) Φ, ▷ (∀ b : Bool, Φ #b) -∗ WP (methods g.ty "Enabled" g.v) f {{ Φ }}

- `k8s_io.apiserver.pkg.storage.feature.DefaultFeatureSupportChecker_init`
  (`Proof/k8s_io/apiserver/pkg/storage/feature/Init.lean:55-57`), whose postcondition is
  `checkerInit` (`Base.lean:68-74`), `storage/feature`'s `isPkgInit` fact (`Base.lean:312-314`):

      □ ∀ (ctx cl f : val) Φ, ▷ Φ #() -∗
        WP (MethodResolve FeatureSupportChecker "CheckClient" (load DefaultFeatureSupportChecker))
             ctx cl f {{ Φ }}

Used by `etcd3.New` (`New.lean:66-75,155`), `store.Delete` (`store__Delete.lean:59-80`) and
`NewCompactor` (`NewCompactor.lean:54`); reach per the sweep plan: 4/4 k8s `_safe` results each.

Go: `k8s.io/component-base@v0.0.0-20261018214756-cd2c1afd246a` (`featuregate/feature_gate.go`),
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (`pkg/util/feature/feature_gate.go`,
`pkg/storage/feature/feature_support_checker.go`), as `examples/k8s/compactor/go.mod` pins them;
`GOTOOLCHAIN=go1.27.3`.

## Verdict

**Both refuted (Go side); Lean side not yet built.**

1. `featureInit`'s `Enabled` answers for **any** `f`. Go's `featureGate.Enabled`
   (`feature_gate.go:947-952`) calls `featureEnabled` (`:933-944`), which panics
   (`"feature %q is not registered in FeatureGate"`) for a key neither set nor known; the docstring
   says so ("If the key is not known, this call will panic", `:946`). `DefaultFeatureGate` is
   `DefaultMutableFeatureGate = featuregate.NewFeatureGate()` (`util/feature/feature_gate.go:28,32`);
   its known keys are only those registered by other packages' `init`s (`k8s.io/apiserver/pkg/
   features`), never an arbitrary string.
2. `checkerInit`'s `CheckClient` returns for **any** client. Go's `CheckClient`
   (`feature_support_checker.go:113-120`) with `RequestWatchProgress` calls `checkClient`, which
   ranges over `c.Endpoints()` (`:142`): a nil `client` interface is a nil dereference, and so is a
   typed-nil `*clientv3.Client` (`client.go:167-170` reads `c.epMu`). (Not run, also outside the
   fact: a client whose `Status` panics, in the goroutines of `:147-156`, which
   `HandleCrashWithContext` re-panics.)

## The program

`examples/axiomcx/k8s-featureinit/featureinit.go` (a module of its own, as
`examples/k8s/compactor`, whose `go.mod`/`go.sum` it copies with only the module path changed; the
examples module does not require `k8s.io/apiserver`):

    func Main() {
        utilfeature.DefaultFeatureGate.Enabled("NoSuchFeature")
    }

    func CheckNil() {
        feature.DefaultFeatureSupportChecker.CheckClient(nil, nil, storage.RequestWatchProgress)
    }

Test (`cd examples/axiomcx/k8s-featureinit && GOPROXY=off go test . -run . -count=1 -v`, go1.27.3):

    === RUN   TestMainPanics
        k8s-featureinit_test.go:25: Main panicked: feature "NoSuchFeature" is not registered in FeatureGate
    --- PASS: TestMainPanics (0.00s)
    === RUN   TestCheckNilPanics
        k8s-featureinit_test.go:25: CheckNil panicked: runtime error: invalid memory address or nil pointer dereference
    --- PASS: TestCheckNilPanics (0.00s)
    === RUN   TestCheckNilClientPtrPanics
        k8s-featureinit_test.go:25: CheckNilClientPtr panicked: runtime error: invalid memory address or nil pointer dereference
    --- PASS: TestCheckNilClientPtrPanics (0.00s)
    PASS

(`TestCheckNilClientPtrPanics`: `context.Background()` and a typed-nil `*clientv3.Client`.)

## Why the premises hold, and the proof (not yet built)

Neither fact has a premise a program must show: both are facts of the packages' `isPkgInit`,
which the program's own `isPkgInit` includes (its imports'), so the theorem
`{{ isPkgInit pkg_id.<featureinit> }} @! featureinit.Main #() {{ RET #(); True }}` takes nothing
else. The steps are the ones the existing proofs use:

- `Main`: `ihave #Pft : isPkgInit pkg_id.k8s_io.apiserver.pkg.util.feature $$ []` (`iPkgInit`),
  `ihave #Hft : featureInit $$ []` (`iapply isPkgInit_access $$ Pft`),
  `icases Hft with ⟨%g, #Hg, #Hen⟩`; `wp_auto` loads `DefaultFeatureGate` through `Hg` and resolves
  the interface method to `methods g.ty "Enabled" g.v`; `wp_apply Hen as %b` at `f :=` the
  converted literal `"NoSuchFeature"` (any `val`), then the result is discarded. As
  `store__Delete.lean:57-80`.
- `CheckNil`: `isPkgInit pkg_id.k8s_io.apiserver.pkg.storage.feature` gives `checkerInit`
  (`isPkgInit_access`); `isPkgInit` of `storage` gives `storageInit` (`RequestWatchProgress ↦□ rw`)
  for the argument's load; `wp_apply Chk` at `ctx := ` nil, `cl := ` nil (any `val`s). As
  `New.lean:71-75,155`.
- `#print axioms` should list `DefaultFeatureGate_init` (resp. `DefaultFeatureSupportChecker_init`)
  through the `isPkgInit` instance only if the theorem is closed by adequacy; the triple itself
  rests on the instances' definitions (`define_is_pkg_init featureInit`), so in the triple form
  the axioms enter only in the closed theorem, where the package's `wp_initialize'` uses them.
  Phase 2 should state the closed form (or take the two `*_init` axioms' consequence as the
  hypothesis the triple's `isPkgInit` stands for) so the refuted axiom is visible in
  `#print axioms`.

Where it could get stuck: a Goose project for this package must reach the k8s translation
(project `k8s-apiserver`, names-only `component-base/featuregate`), as
`examples/k8s/compactor`'s does; the `Feature` conversion of the literal must reduce under
`wp_auto` (it is a string-to-named-string conversion).

## Proposed restatement (not applied)

- `featureInit`: `Enabled f` answers only for a registered key: a persistent `featureKnown s`
  for each key `k8s.io/apiserver/pkg/features`' `init` registers (a fact of that package's
  `isPkgInit`, which `etcd3` imports), and the WP takes `f = #s` with `featureKnown s`. The callers
  ask `ListFromCacheSnapshot` and `AllowUnsafeMalformedObjectDeletion`, both registered there.
- `checkerInit`: `CheckClient` takes `cl` a non-nil client meeting `Endpoints`/`Status` specs that
  do not panic (etcd3.New passes its `*clientv3.Client`, which `isClient`-style facts cover), and
  `ctx` a context.
