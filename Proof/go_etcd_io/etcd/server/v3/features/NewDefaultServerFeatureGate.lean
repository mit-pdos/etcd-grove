/-
The trust boundary: `features.NewDefaultServerFeatureGate` (`server/v3/features` and
`pkg/v3/featuregate` are names-only; see the spec's header for why the contract holds of Go).
Added 2026-10-18 (item 9, point 7: the adequacy example's configuration).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom features.NewDefaultServerFeatureGate.wp_proof :
  features.NewDefaultServerFeatureGate.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
