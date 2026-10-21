/-
Trust boundary: `io.Copy` to `io.Discard` (an axiom; see `Spec/io/Copy.lean`).
-/
module

public import Spec.io.Copy

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

/-- **Trust boundary** (`notes/decisions.md` D26, proposed): `io.Copy(io.Discard, src)` reads
`src` until a read fails (`src`'s `WriteTo`, a `*net.TCPConn`'s, or `io.Discard`'s `ReadFrom`,
or `copyBuffer`'s loop: each only reads `src` and writes to the discarding writer), and
returns. It is not translated (Perennial's `io` translates its types and `Discard`). -/
axiom io.Copy.wp_proof : io.Copy.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
