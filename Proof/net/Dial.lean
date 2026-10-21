/-
Trust boundary: `net.Dial` (an axiom; see `Spec/net/Dial.lean`).
-/
module

public import Spec.net.Dial

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

/-- **Trust boundary** (`notes/decisions.md` D26, proposed): `net.Dial("tcp", addr)` resolves
`addr` and connects a TCP socket to it, returning a `*net.TCPConn` as a `net.Conn`, or an error
(refused, unreachable, unresolvable). The connection is new: nothing has read or written it. -/
axiom net.Dial.wp_proof : net.Dial.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
