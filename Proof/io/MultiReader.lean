/-
Trust boundary: `io.MultiReader` (an axiom; see `Spec/io/MultiReader.lean`). rafthttp stage 7d, 2026-10-24, D42.
-/
module

public import Spec.io.MultiReader

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

/-- **Trust boundary**: `io.MultiReader(buf, rc)` (names only in Perennial) reads `buf` to its end, then `rc` to its end, returning `EOF` only after `rc`'s: the stream contract of `Spec/io/MultiReader.lean`. What would discharge it: Perennial's `io.MultiReader` translated, and `readerStreams`' meaning as a `Read` contract. -/
axiom io.MultiReader.wp_proof : io.MultiReader.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
