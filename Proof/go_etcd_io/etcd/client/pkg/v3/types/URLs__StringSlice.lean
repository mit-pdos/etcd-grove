/-
The trust boundary: `types.URLs.StringSlice()`: names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice

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

axiom types.URLs.StringSlice.wp_proof : types.URLs.StringSlice.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
