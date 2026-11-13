/-
The trust boundary: `encoding/binary`'s `Read` of an `*int64`, little-endian (names-only in
Perennial: `Read` goes through `reflect`; see `Spec/encoding/binary/ReadInt64LE.lean`). As
`binary.ReadUint64.wp_proof`; the proposed Perennial change is `notes/perennial-changes.md`,
"`encoding/binary`'s `Write`/`Read`". **Pending the user's review** (WAL leaf specs, 2026-11-13).
-/
module

public import Spec.encoding.binary.ReadInt64LE

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom binary.ReadInt64LE.wp_proof : binary.ReadInt64LE.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
