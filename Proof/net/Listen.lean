/-
Trust boundary: `net.Listen` (an axiom; see `Spec/net/Listen.lean`).
-/
module

public import Spec.net.Listen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): `net.Listen("tcp", addr)` binds and listens on a
TCP socket at `addr` (resolved), returning a `*net.TCPListener` as a `net.Listener`, or an error
(the address in use, not permitted, unresolvable). Connections dialed to `addr` reach the listener:
`netAddrFree` says no other socket holds the address, the closed-world assumption of `InvNet.lean`. -/
axiom net.Listen.wp_proof : net.Listen.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
