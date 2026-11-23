/-
**The server's feature gate** (`featuregate.FeatureGate`, a contract), as the server's proofs see
it. Lean-first (no Rocq counterpart). (Until 2026-11-23 the trust boundary; since featuregate-3
`NewDefaultServerFeatureGate` is proved to return a gate meeting it, over featuregate's own specs,
`Spec/go_etcd_io/etcd/pkg/v3/featuregate/`.) Also the package fact `featuresInit` and the server's
features' specs `serverFeatureSpecs`.

* `serverFeatures`: the features `features.NewDefaultServerFeatureGate` registers (the keys of
  `DefaultEtcdServerFeatureGates`, `server/features/etcd_features.go`).
* `isFeatureGate fg`: `fg` has some registered features `K`, the server's among them, and its
  `Enabled(f)` returns some boolean for every registered feature `f`, its `GetAll()` a fresh map of
  `K`. (`featureGate.Enabled` panics on a feature not registered, `pkg/featuregate/feature_gate.go`:
  until 2026-10-18 the contract was stated for every `f`, which no Go feature gate meets;
  `notes/STATUS.md`, "Item 9, point 7".) The server asks `Enabled` of its own features
  (`StopGRPCServiceOnDefrag`, `TxnModeWriteWithSharedBuffer`, `LeaseCheckpoint`,
  `LeaseCheckpointPersist`, `PriorityRequest` on the verified paths) and, in
  `addFeatureGateMetrics`, of every feature `GetAll` returns (featuregate's own `AllAlpha` and
  `AllBeta` too: featuregate-4, 2026-11-23, `notes/specs-only/ledger.md`), each name and `PreRelease`
  valid UTF-8 (`featureLabelsOk`: the gauge vector's `With` panics otherwise).
* `featureIs fg f b`: `fg`'s `Enabled(f)` returns `b` (audit B4a: `CompactHashCheck` off, for
  `EtcdServer.monitorCompactHash`).

Moved from `etcdserver/InvProposer.lean` (2026-10-18) so that `features.NewDefaultServerFeatureGate`'s
spec states it without importing the server's proofs.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Proof.go_etcd_io.etcd.pkg.v3.featuregate.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.features
public import Proof.unicode.utf8.Valid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `DefaultEtcdServerFeatureGates` (`server/features/etcd_features.go`), in the initializer's
insertion order (featuregate-3, 2026-11-23). -/
def serverFeatureSpecs [GooseExts] : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec :=
  <[go!"NonBlockingDefrag" := featuregate.spec true go!"BETA"]>
  (<[go!"PriorityRequest" := featuregate.spec false go!"ALPHA"]>
  (<[go!"FastLeaseKeepAlive" := featuregate.spec true go!"BETA"]>
  (<[go!"SetMemberLocalAddr" := featuregate.spec false go!"ALPHA"]>
  (<[go!"LeaseCheckpointPersist" := featuregate.spec false go!"ALPHA"]>
  (<[go!"LeaseCheckpoint" := featuregate.spec false go!"ALPHA"]>
  (<[go!"TxnModeWriteWithSharedBuffer" := featuregate.spec true go!"BETA"]>
  (<[go!"CompactHashCheck" := featuregate.spec false go!"ALPHA"]>
  (<[go!"InitialCorruptCheck" := featuregate.spec false go!"ALPHA"]>
  (<[go!"StopGRPCServiceOnDefrag" := featuregate.spec false go!"ALPHA"]> ∅)))))))))

/-- **`server/v3/features`' package fact** (featuregate-3, 2026-11-23; until then `True`):
`DefaultEtcdServerFeatureGates` holds a read-only map of `serverFeatureSpecs`, for good (nothing
writes it after the initializer; `NewDefaultServerFeatureGate` passes it to `Add`, which only
reads it). -/
def featuresInit : IProp GF :=
  iprop(∃ m : Loc, typedPointsto (globalAddr go_etcd_io.etcd.server.v3.features.DefaultEtcdServerFeatureGates)
    m DFrac.discard ∗ m ↦$□ serverFeatureSpecs)

instance featuresInit_persistent : Persistent (featuresInit (GF := GF)) := by
  unfold featuresInit; infer_instance

end init

/-- The registered features `K` make valid metric labels: each name and `PreRelease` is valid UTF-8
(`addFeatureGateMetrics` passes both to a gauge vector's `With`). -/
def featureLabelsOk [GooseExts] (K : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec) : Prop :=
  ∀ f s, K !! f = some s → utf8Valid f ∧ utf8Valid s.PreRelease'

theorem featureLabelsOk_empty [GooseExts] : featureLabelsOk ∅ := by
  intro f s h; simp at h

theorem featureLabelsOk_insert [GooseExts] (K : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (k : GoString) (v : go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (hk : utf8Valid k) (hv : utf8Valid v.PreRelease') (hK : featureLabelsOk K) :
    featureLabelsOk (<[k := v]> K) := by
  intro f s h
  rw [GMap.lookup_insert_eq_iff] at h
  by_cases hkf : k = f
  · subst hkf; simp at h; subst h; exact ⟨hk, hv⟩
  · simp only [hkf, ↓reduceIte] at h; exact hK f s h

theorem featureLabelsOk_union [GooseExts] (A B : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec)
    (hA : featureLabelsOk A) (hB : featureLabelsOk B) : featureLabelsOk (A ∪ B) := by
  intro f s h
  rw [GMap.lookup_union] at h
  cases hAf : A !! f with
  | some a => rw [hAf] at h; simp at h; subst h; exact hA f a hAf
  | none => rw [hAf] at h; simp at h; exact hB f s h

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The features `NewDefaultServerFeatureGate` registers (`DefaultEtcdServerFeatureGates`'s keys). -/
def serverFeatures : List GoString :=
  [go!"StopGRPCServiceOnDefrag", go!"InitialCorruptCheck", go!"CompactHashCheck",
   go!"TxnModeWriteWithSharedBuffer", go!"LeaseCheckpoint", go!"LeaseCheckpointPersist",
   go!"SetMemberLocalAddr", go!"FastLeaseKeepAlive", go!"PriorityRequest",
   go!"NonBlockingDefrag"]

/-- **The feature gate** `fg` (`featuregate.FeatureGate`, a contract), with some registered features
`K`, the server's among them, whose names and `PreRelease`s are valid UTF-8: `Enabled(f)` of a
registered feature returns some boolean, and `GetAll()` returns a fresh map of `K` (featuregate-4,
2026-11-23; until then only `Enabled`, of the server's features). -/
def isFeatureGate (fg : GoInterface) : IProp GF :=
  iprop(∃ (fi : GoInterfaceOk) (K : GMap GoString go_etcd_io.etcd.pkg.v3.featuregate.FeatureSpec),
    ⌜fg = GoInterface.ok fi⌝ ∗
    ⌜(∀ f ∈ serverFeatures, (K !! f).isSome) ∧ featureLabelsOk K⌝ ∗
    □ (∀ f : GoString,
      {{ ⌜(K !! f).isSome⌝ }} (App (Val #(methods fi.ty go!"Enabled" fi.v)) (Val #f))
      {{ (b : Bool), RET #b; True }}) ∗
    □ ({{ True }} (App (Val #(methods fi.ty go!"GetAll" fi.v)) (Val #()))
      {{ (m : Loc), RET #m; m ↦$ K }}))

instance isFeatureGate_persistent (fg : GoInterface) : Persistent (isFeatureGate (GF := GF) fg) := by
  unfold isFeatureGate; infer_instance

/-- **`fg`'s `Enabled(f)` answers `b`** (persistent; audit B4a, 2026-10-18): a fact of the feature
gate `NewDefaultServerFeatureGate` returns, for a feature whose default it is (no feature is set
in the program). `EtcdServer.monitorCompactHash`'s contract takes it of `CompactHashCheck` (off by
default), under which the monitor returns at once. -/
def featureIs (fg : GoInterface) (f : GoString) (b : Bool) : IProp GF :=
  iprop(∃ fi : GoInterfaceOk, ⌜fg = GoInterface.ok fi⌝ ∗
    □ ({{ True }} (App (Val #(methods fi.ty go!"Enabled" fi.v)) (Val #f)) {{ RET #b; True }}))

instance featureIs_persistent (fg : GoInterface) (f : GoString) (b : Bool) :
    Persistent (featureIs (GF := GF) fg f b) := by
  unfold featureIs; infer_instance

end defs

end EtcdGrove
end Perennial
