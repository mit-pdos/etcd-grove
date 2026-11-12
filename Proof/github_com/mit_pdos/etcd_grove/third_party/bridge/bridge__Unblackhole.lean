module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Unblackhole

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **Trust boundary** (D26: the bridge is part of the network, its code not verified).
`Unblackhole` closes every connection, waits for their goroutines, and makes a fresh `blackholec`;
later connections copy again. -/
axiom bridge.Unblackhole.wp_proof : bridge.Unblackhole.spec (GF := GF) (hG := hG)

end proof

end bridge
end EtcdGrove
end Perennial
