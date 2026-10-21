module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.New

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

/-- **Trust boundary** (D26: the bridge is part of the network, its code not verified). The bridge
accepts on `l` and, per accepted connection, dials `addr` and copies bytes between the two, both
ways, until a copy fails, the bridge is blackholed or its connections dropped; a client of `a` thus
reaches `addr`'s server through connections that deliver a prefix of each side's bytes, which gRPC
sees as `addr`'s server or as a failed attempt (D26). Its goroutines do not panic (the wait group
counts at most one goroutine per live connection, far below its `2^31` bound). -/
axiom New.wp_proof : New.spec (GF := GF) (hG := hG)

end proof

end bridge
end EtcdGrove
end Perennial
