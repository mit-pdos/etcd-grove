module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__DropConnections

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **Trust boundary** (D26: the bridge is part of the network, its code not verified).
`DropConnections` closes every connection and waits for their goroutines; the bridge keeps
accepting. -/
axiom bridge.DropConnections.wp_proof : bridge.DropConnections.spec (GF := GF) (hG := hG)

end proof

end bridge
end EtcdGrove
end Perennial
