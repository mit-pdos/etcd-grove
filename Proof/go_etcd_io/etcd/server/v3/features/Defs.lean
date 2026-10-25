/-
**The server's feature gate** (`featuregate.FeatureGate`, names-only: the trust boundary, a
contract), as the server's proofs see it. Lean-first (no Rocq counterpart).

* `serverFeatures`: the features `features.NewDefaultServerFeatureGate` registers (the keys of
  `DefaultEtcdServerFeatureGates`, `server/features/etcd_features.go`).
* `isFeatureGate fg`: `fg`'s `Enabled(f)` returns some boolean for every registered feature `f`.
  (`featureGate.Enabled` panics on a feature not registered, `pkg/featuregate/feature_gate.go`:
  until 2026-10-18 the contract was stated for every `f`, which no Go feature gate meets;
  `notes/STATUS.md`, "Item 9, point 7".) The server asks only for registered features
  (`StopGRPCServiceOnDefrag`, `TxnModeWriteWithSharedBuffer`, `LeaseCheckpoint`,
  `LeaseCheckpointPersist`, `PriorityRequest` on the verified paths).
* `featureIs fg f b`: `fg`'s `Enabled(f)` returns `b` (audit B4a: `CompactHashCheck` off, for
  `EtcdServer.monitorCompactHash`).

Moved from `etcdserver/InvProposer.lean` (2026-10-18) so that `features.NewDefaultServerFeatureGate`'s
spec states it without importing the server's proofs.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The features `NewDefaultServerFeatureGate` registers (`DefaultEtcdServerFeatureGates`'s keys). -/
def serverFeatures : List GoString :=
  [go!"StopGRPCServiceOnDefrag", go!"InitialCorruptCheck", go!"CompactHashCheck",
   go!"TxnModeWriteWithSharedBuffer", go!"LeaseCheckpoint", go!"LeaseCheckpointPersist",
   go!"SetMemberLocalAddr", go!"FastLeaseKeepAlive", go!"PriorityRequest",
   go!"NonBlockingDefrag", go!"DefragmentedSnapshot"]

/-- **The feature gate** `fg` (`featuregate.FeatureGate`, names-only: the trust boundary, a
contract): `Enabled(f)` of a registered feature returns some boolean. -/
def isFeatureGate (fg : GoInterface) : IProp GF :=
  iprop(∃ fi : GoInterfaceOk, ⌜fg = GoInterface.ok fi⌝ ∗
    □ (∀ f : GoString,
      {{ ⌜f ∈ serverFeatures⌝ }} (App (Val #(methods fi.ty go!"Enabled" fi.v)) (Val #f))
      {{ (b : Bool), RET #b; True }}))

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
