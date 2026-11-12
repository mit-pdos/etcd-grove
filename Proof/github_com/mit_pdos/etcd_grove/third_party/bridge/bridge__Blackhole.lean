module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__Blackhole

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

/-- **Trust boundary** (D26: the bridge is part of the network, its code not verified). `Blackhole`
closes `blackholec` under the mutex: every copy goroutine stops copying (its `select` sees the
channel closed), so no bytes pass until `Unblackhole`. -/
axiom bridge.Blackhole.wp_proof : bridge.Blackhole.spec (GF := GF) (hG := hG)

end proof

end bridge
end EtcdGrove
end Perennial
