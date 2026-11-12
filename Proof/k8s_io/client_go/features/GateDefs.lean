/-
client-go's feature gates (`k8s.io/client-go/features`), as the informer layer reads them: a
premise, not a fact. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`.

`features`' initialization is names only (gap C7, `notes/k8s-clientgo-goose.md`): its package
fact is `True`, so what `FeatureGates()` returns is unknown to the proofs. Under the DaemonSet
example (`dsmain.Main`) the gates are kube-controller-manager's: `k8s.io/kubernetes/pkg/features`'
init replaces client-go's by an adapter over component-base's gate, on which `Main` sets
`WatchListClient` off and `AtomicFIFO` on; `InOrderInformers` is GA and locked on,
`InOrderInformersBatchProcess` and `UnlockWhileProcessingFIFO` beta and on by default. A spec that
reads a gate takes `gateIs f b` (the gate `f` answers `b`) as a premise, which the closed theorem
discharges from a model of that gate (phase 6).
-/
module

public import GeneratedProof.k8s_io.client_go.features
public import Perennial.Proof.ProofPrelude

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace features

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The feature gate `f` answers `b`** (persistent): `FeatureGates()` returns gates whose
`Enabled(f)` returns `b`. -/
def gateIs (f : val) (b : Bool) : IProp GF :=
  iprop({{ True }}
    (App (Val (@! k8s_io.client_go.features.FeatureGates)) (Val #()))
    {{ (g : GoInterface), RET #g; ∃ i : GoInterfaceOk, ⌜g = .ok i⌝ ∗
      {{ True }} (App (Val #(methods i.ty go!"Enabled" i.v)) (Val f)) {{ RET #b; True }} }})

instance gateIs_persistent (f : val) (b : Bool) : Persistent (gateIs (GF := GF) f b) := by
  unfold gateIs; infer_instance

end defs

end features
end EtcdGrove
end Perennial
