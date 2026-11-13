/-
**The default feature gate's specs** (sweep repairs 1, B5, joint with k8s 7e's gate-state fact;
2026-11-08, the design approved by etcd-grove-81, `/shared/tmp/sweep-repairs-1/b5-r1.md`).
Lean-first. The trust boundary: `k8s.io/component-base/featuregate` is names-only, so the gate's
`Enabled` and `Set` are specified here, inside the persistent `featureGateOk g`, which only
`k8s.io/apiserver/pkg/features`' registration (`features.init_0_ok`, its `Init.lean`) gives.

What Go does (`component-base/featuregate/feature_gate.go` at the pin): `util/feature`'s
`DefaultMutableFeatureGate = featuregate.NewFeatureGate()` and `DefaultFeatureGate =
DefaultMutableFeatureGate` hold one `*featureGate`; `features`' `init` registers its features with
it (`AddVersioned`, under `runtime.Must`). `Enabled(k)` of a registered `k` returns the value set
for `k` if any, else the default at the emulated version, and of an unregistered one panics.
`Set("k=false")` parses the string, then under the gate's lock stores the new set values only if
no check failed (`SetFromMapWithLogger`, `:507-511`); it fails for an unknown key, a feature locked
to its default, a feature `PreAlpha` at the emulated version, or a dependency check.

`Set("k=true")` (k8s 7f-5, T5-c, `notes/k8s-7f5-freeze.md`): the same, with `true`; the driver turns
`WatchList` on so (`watchList`, after `noStreaming`). A `Set` of another feature keeps an earlier
one's value: `SetFromMapWithLogger` re-applies every pair set before (`enabledRaw`).

**One value per feature** (k8s 7f-5, S1 review, decided by etcd-grove-81): `Set` is specified only
for a feature's value in the table `k8sSetValue` (`WatchList` true, the other queried features
false), so `featureOn g s` and `featureOff g s` of one `s` are never both given: a `Set(s=true)` then
`Set(s=false)`, after which `Enabled(s)` answers `false` in Go (`examples/premisefix/watcherctx`,
scenario `true-then-false`), has no spec.

**The environment assumption** (restated by k8s 7f-5's S1 review, decided by etcd-grove-81; checked
over the programs' compiled closures by `etc/featuregate-check.py`, in `etc/gates.sh`, with each hit's
verdict in `etc/featuregate-allow.txt`; first checked 2026-11-08, `b5-r1.md` "The no-other-mutator
check"): **no code of the program mutates the gate but `Set`s of the table's values** (repeats of
one are harmless), **each made before any `Enabled` of its feature**. Nothing else runs: `SetFromMap*`,
`SetEmulationVersion*`, `OverrideDefault*`, `ResetFeatureValueToDefault`, `Add`/`AddVersioned`/
`AddDependencies` after registration, `AddFlag` (flag parsing calls `Set`), `DeepCopyAndReset`-and-
replace, `featuregatetesting`, and no code reassigns either variable. The order matters to
`Enabled`'s triple: it hands its caller a wand `featureOff g s -∗ ⌜b = false⌝` (and the `featureOn`
one), which the caller may keep; an `Enabled(s)` before the `Set` answers the default at the emulated
version (scenario `enabled-then-set`: `true` of `WatchList`; `EtcdRangeStream`'s is `true` from 1.37,
`kube_features.go:436-437`), and the kept wand would turn a
later `featureOff g s` into `true = false`. The check covers the k8s etcd3 driver and the compactor;
the DaemonSet program (`examples/k8s/daemonset/dsmain`) mutates the gate (`SetFromMap`,
`k8s.io/kubernetes/pkg/features`' registration), so the assumption is not claimed of it, and the
script refuses any Lean module of its tree that names these specs.
-/
module

public import GeneratedProof.k8s_io.apiserver.pkg.util.feature

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8sfeature

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The features the verified programs ask the default gate about (etcd3's `Enabled` calls:
`store.go:202,416,758`, `watcher.go:197,227,238,310,547`, `compact.go:98`), all registered by
`k8s.io/apiserver/pkg/features`' `init`, none special (`AllAlpha`/`AllBeta`), none containing `,`
or `=` (so `Set`'s parse of `s ++ "=false"` is the pair `(s, false)`). An `Enabled` of any other
key has no spec: of an unregistered one Go panics. -/
def k8sQueriedFeatures : List GoString :=
  [go!"AllowUnsafeMalformedObjectDeletion", go!"ListFromCacheSnapshot", go!"EtcdRangeStream",
   go!"WatchList", go!"ConcurrentWatchObjectDecode"]

/-- **`Set(s=false)` succeeded on the gate `g`** (opaque, persistent): `g`'s set value of `s` is
`false`, for the rest of the run (no code sets it back: the file header's assumption). Given only
by `featureGateOk`'s `Set` triple, for an `s` whose `k8sSetValue` is `false`. -/
opaque featureOff (g : GoInterfaceOk) (s : GoString) : IProp GF

/-- It is persistent (a fact of the run, once true). -/
axiom featureOff_persistent (g : GoInterfaceOk) (s : GoString) :
    Persistent (featureOff (GF := GF) g s)

attribute [instance] featureOff_persistent

/-- **`Set(s=true)` succeeded on the gate `g`** (opaque, persistent; k8s 7f-5, T5-c): `g`'s set value
of `s` is `true`, for the rest of the run (the file header's assumption). Given only by
`featureGateOk`'s `Set` triple, for an `s` whose `k8sSetValue` is `true` (`WatchList`). -/
opaque featureOn (g : GoInterfaceOk) (s : GoString) : IProp GF

/-- It is persistent (a fact of the run, once true). -/
axiom featureOn_persistent (g : GoInterfaceOk) (s : GoString) :
    Persistent (featureOn (GF := GF) g s)

attribute [instance] featureOn_persistent

/-- What `Set(s ++ "=" ++ b)` gives: `featureOn` for `true`, `featureOff` for `false`. -/
def featureSet (g : GoInterfaceOk) (s : GoString) (b : Bool) : IProp GF :=
  if b then featureOn g s else featureOff g s

instance featureSet_persistent (g : GoInterfaceOk) (s : GoString) (b : Bool) :
    Persistent (featureSet (GF := GF) g s b) := by
  unfold featureSet; split <;> infer_instance

/-- The string `Set` parses as the pair `(s, b)`. -/
def setArg (s : GoString) (b : Bool) : GoString :=
  s ++ (if b then go!"=true" else go!"=false")

/-- **The one value each queried feature may be set to** (k8s 7f-5, S1 review): `WatchList` `true`
(the driver's `watchList`), every other feature of `k8sQueriedFeatures` `false` (sweep repairs 1, B5:
the driver's `noStreaming` sets `EtcdRangeStream`); `none` off the list. `Set` is specified only for
these values, so `featureOn` and `featureOff` of one feature are never both given. -/
def k8sSetValue (s : GoString) : Option Bool :=
  if s = go!"WatchList" then some true
  else if s ∈ k8sQueriedFeatures then some false
  else none

/-- **`g` is the process's default feature gate, its features registered** (persistent): the
`*featureGate` `util/feature`'s `DefaultMutableFeatureGate` and `DefaultFeatureGate` both hold
(`GoInterface.ok g`), after `k8s.io/apiserver/pkg/features`' `init` registered its features.
- `Enabled(s)`, for `s ∈ k8sQueriedFeatures`, returns some `bool`: `false` once `featureOff g s`
  holds, `true` once `featureOn g s` holds.
- `Set(s ++ "=" ++ v)` (`setArg s v`), for `v` the table's value of `s` (`k8sSetValue s = some v`),
  returns `nil` and gives `featureSet g s v` (`featureOn g s` for `true`, `featureOff g s` for
  `false`), or returns a non-nil error. A failed `Set` does not store the map `Enabled` reads
  (`enabled`), but it does store the raw pair in `enabledRaw` (`feature_gate.go:498-504`, before the
  checks), which every later `Set` re-applies: a later `Set` then fails too (scenario `failed-set`),
  or, if what failed was a dependency check, may succeed and apply the pair. Neither is excluded here: the error arm gives nothing, and a
  pair re-applied so is of a table value, of which no contrary fact is ever given.
Under the file header's environment assumption. (Until sweep repairs 1, B5: `Enabled` answered any
`bool` for any key, false of an unregistered one, and nothing was said of `Set`. Until k8s 7f-5:
only `Set(s=false)` and `featureOff`. Until 7f-5's S1 review: `Set(s=b)` of either `b`.) -/
def featureGateOk (g : GoInterfaceOk) : IProp GF :=
  iprop(
    (□ ∀ (s : GoString) (Φ : val → IProp GF), ⌜s ∈ k8sQueriedFeatures⌝ →
        ▷ (∀ b : Bool, ((featureOff g s -∗ ⌜b = false⌝) ∧ (featureOn g s -∗ ⌜b = true⌝)) -∗
          Φ #b) -∗
        WP (App (Val #(methods g.ty go!"Enabled" g.v)) (Val #s)) {{ Φ }}) ∗
    (□ ∀ (s : GoString) (v : Bool) (Φ : val → IProp GF), ⌜k8sSetValue s = some v⌝ →
        ▷ (∀ err : GoInterface,
            (⌜err = GoInterface.nil⌝ ∗ featureSet g s v ∨ ⌜err ≠ GoInterface.nil⌝) -∗ Φ #err) -∗
        WP (App (Val #(methods g.ty go!"Set" g.v)) (Val #(setArg s v))) {{ Φ }}))

instance featureGateOk_persistent (g : GoInterfaceOk) :
    Persistent (featureGateOk (GF := GF) g) := by
  unfold featureGateOk; infer_instance

end defs

end k8sfeature
end EtcdGrove
end Perennial
