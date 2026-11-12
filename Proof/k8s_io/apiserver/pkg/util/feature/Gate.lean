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

The environment assumption (checked over the examples' compiled closure, 2026-11-08: `b5-r1.md`,
"The no-other-mutator check"): no code of the program other than the `Set(s=false)` calls these
specs cover changes the gate's set values (`Set` with `true`, `SetFromMap`, `SetEmulationVersion*`,
`OverrideDefault*`, `Add*` after registration, `DeepCopyAndReset`-and-replace, `featuregatetesting`)
or reassigns either variable.
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
by `featureGateOk`'s `Set` triple. -/
opaque featureOff (g : GoInterfaceOk) (s : GoString) : IProp GF

/-- It is persistent (a fact of the run, once true). -/
axiom featureOff_persistent (g : GoInterfaceOk) (s : GoString) :
    Persistent (featureOff (GF := GF) g s)

attribute [instance] featureOff_persistent

/-- **`g` is the process's default feature gate, its features registered** (persistent): the
`*featureGate` `util/feature`'s `DefaultMutableFeatureGate` and `DefaultFeatureGate` both hold
(`GoInterface.ok g`), after `k8s.io/apiserver/pkg/features`' `init` registered its features.
- `Enabled(s)`, for `s ∈ k8sQueriedFeatures`, returns some `bool`, and `false` once
  `featureOff g s` holds.
- `Set(s ++ "=false")`, for `s ∈ k8sQueriedFeatures`, returns `nil` and gives `featureOff g s`, or
  returns a non-nil error (and changes nothing `Enabled` reads).
Under the file header's environment assumption. (Until sweep repairs 1, B5: `Enabled` answered any
`bool` for any key, false of an unregistered one, and nothing was said of `Set`.) -/
def featureGateOk (g : GoInterfaceOk) : IProp GF :=
  iprop(
    (□ ∀ (s : GoString) (Φ : val → IProp GF), ⌜s ∈ k8sQueriedFeatures⌝ →
        ▷ (∀ b : Bool, (featureOff g s -∗ ⌜b = false⌝) -∗ Φ #b) -∗
        WP (App (Val #(methods g.ty go!"Enabled" g.v)) (Val #s)) {{ Φ }}) ∗
    (□ ∀ (s : GoString) (Φ : val → IProp GF), ⌜s ∈ k8sQueriedFeatures⌝ →
        ▷ (∀ err : GoInterface,
            (⌜err = GoInterface.nil⌝ ∗ featureOff g s ∨ ⌜err ≠ GoInterface.nil⌝) -∗ Φ #err) -∗
        WP (App (Val #(methods g.ty go!"Set" g.v)) (Val #(s ++ go!"=false"))) {{ Φ }}))

instance featureGateOk_persistent (g : GoInterfaceOk) :
    Persistent (featureGateOk (GF := GF) g) := by
  unfold featureGateOk; infer_instance

end defs

end k8sfeature
end EtcdGrove
end Perennial
