/-
**etcd's feature gate** (`pkg/featuregate/feature_gate.go`, `*featureGate`), as its specs see it
(featuregate-3, 2026-11-23). Lean-first (no Rocq counterpart).

A gate's state is two maps, each held by an `atomic.Value` that only ever holds maps of one type:
`known` (`map[Feature]FeatureSpec`, the registered features) and `enabled` (`map[Feature]bool`, the
features set explicitly). The maps themselves are never written once stored (every writer copies
first, `maps.Copy`, and stores the copy), so a stored map is read-only (`↦$□`).

* `ownGate p K E`: the gate `p` while its maker owns it (between `New` and its last `Add`): the
  `Value`s owned (a `Store` needs them whole), `closed` false (`Add` refuses a closed gate), and
  `lock` a mutex with no invariant (`Add` locks it; the owner owns what it guards).
* `isGate p K E`: the gate `p` read-only for good (`Enabled`'s, from any thread): the `Value`s
  persistently held (`ownGate_freeze`; no `Store` can follow).
* `gateValue K E f`: what `Enabled(f)` returns (`enabled[f]` if set, else `known[f].Default`).
* `addCompat F K`: `Add(F)` over the registered `K` succeeds: every feature of `F` that `K` has, it
  has with the same spec.
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.featuregate
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map

namespace featuregate

open _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate in
/-- The map type of `known`. -/
abbrev knownTy [GooseExts] [GoGlobalContext] : go.GoType := go.GoType.MapType Feature.ty FeatureSpec.ty

open _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate in
/-- The map type of `enabled`. -/
abbrev enabledTy [GooseExts] [GoGlobalContext] : go.GoType := go.GoType.MapType Feature.ty go.bool

/-- What `Enabled(f)` returns: `enabled[f]` if set, else `known[f].Default` (`false` for an
unregistered feature, where `Enabled` panics instead). -/
def gateValue [GooseExts] (K : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (E : GMap GoString Bool) (f : GoString) : Bool :=
  match E !! f with
  | some b => b
  | none => match K !! f with
    | some s => s.Default'
    | none => false

/-- `Add(F)` over the registered `K` succeeds: a feature of `F` that `K` has, it has with the same
spec. -/
def addCompat {V : Type} (F K : GMap GoString V) : Prop :=
  ∀ k v, F !! k = some v → K !! k = none ∨ K !! k = some v

/-- `Alpha`'s, `Beta`'s spec: `{Default: d, PreRelease: p}` (`LockToDefault` false). -/
abbrev spec [GooseExts] (d : Bool) (p : GoString) : go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec :=
  ⟨d, false, p⟩

/-- `defaultFeatures`: `AllAlpha` and `AllBeta`, both off by default (`feature_gate.go`), in the
initializer's insertion order. -/
def defaultKnown [GooseExts] : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec :=
  <[go!"AllBeta" := spec false go!"BETA"]> (<[go!"AllAlpha" := spec false go!"ALPHA"]> ∅)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open _root_.Perennial.go_etcd_io.etcd.pkg.v3.featuregate

/-- **The gate `p` while its maker owns it**, with the registered features `K` and the features set
`E` (see the file header). -/
def ownGate (p : Loc) (K : GMap GoString FeatureSpec) (E : GMap GoString Bool) : IProp GF :=
  iprop(∃ (km em : Loc),
    sync.isMutex (structFieldRef featureGate go!"lock" p) iprop(True) ∗
    sync.atomic.ownValue (structFieldRef featureGate go!"known" p) (DFrac.own 1)
      (interface.mkOk knownTy #km) ∗ km ↦$□ K ∗
    sync.atomic.ownValue (structFieldRef featureGate go!"enabled" p) (DFrac.own 1)
      (interface.mkOk enabledTy #em) ∗ em ↦$□ E ∗
    typedPointsto (structFieldRef featureGate go!"closed" p) false (DFrac.own 1))

/-- **The gate `p`, read-only for good**, with the registered features `K` and the features set
`E` (see the file header). -/
def isGate (p : Loc) (K : GMap GoString FeatureSpec) (E : GMap GoString Bool) : IProp GF :=
  iprop(∃ (km em : Loc),
    sync.atomic.ownValue (structFieldRef featureGate go!"known" p) DFrac.discard
      (interface.mkOk knownTy #km) ∗ km ↦$□ K ∗
    sync.atomic.ownValue (structFieldRef featureGate go!"enabled" p) DFrac.discard
      (interface.mkOk enabledTy #em) ∗ em ↦$□ E)

instance ownValue_discard_persistent (u : Loc) (x : GoInterface) :
    Persistent (sync.atomic.ownValue (GF := GF) u DFrac.discard x) := by
  rw [sync.atomic.ownValue_unseal]; unfold sync.atomic.ownValueDef; infer_instance

instance isGate_persistent (p : Loc) (K : GMap GoString FeatureSpec) (E : GMap GoString Bool) :
    Persistent (isGate (GF := GF) p K E) := by
  unfold isGate; infer_instance

/-- **featuregate's package fact**: `defaultFeatures` holds a read-only map of `defaultKnown` and
`specialFeatures` some map, both for good (nothing writes them after the initializer). -/
def featuregateInit : IProp GF :=
  iprop(∃ (dm sm : Loc), typedPointsto (globalAddr defaultFeatures) dm DFrac.discard ∗
    dm ↦$□ defaultKnown ∗ typedPointsto (globalAddr specialFeatures) sm DFrac.discard)

instance featuregateInit_persistent : Persistent (featuregateInit (GF := GF)) := by
  unfold featuregateInit; infer_instance

/-- The maker gives the gate up: it is read-only for good. -/
theorem ownGate_freeze (p : Loc) (K : GMap GoString FeatureSpec) (E : GMap GoString Bool) :
    ownGate (GF := GF) p K E ⊢ |==> isGate p K E := by
  unfold ownGate isGate
  iintro ⟨%km, %em, -, Hk, #HK, He, #HE, -⟩
  rw [sync.atomic.ownValue_unseal]
  unfold sync.atomic.ownValueDef
  ipersist Hk
  ipersist He
  imodintro
  iexists km, em
  isplitl []
  · iexact Hk
  isplitl []
  · iexact HK
  isplitl []
  · iexact He
  · iexact HE

end defs

end featuregate

end EtcdGrove
end Perennial
