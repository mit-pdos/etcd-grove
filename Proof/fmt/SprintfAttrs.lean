/-
The trust boundary: `fmt.Sprintf` of a `membership.Attributes` (`Spec/fmt/SprintfAttrs.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfAttrs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary**: Go's `fmt` formats a struct with `%+v` by reflection over its fields
(here a `string` and a `[]string`, whose elements it reads); `membership.Attributes` has no
methods (`Error`, `String`, `Format`, `GoString`: `server/etcdserver/api/membership/member.go`),
so `Sprintf` calls no code of etcd's, neither panics nor writes memory, and returns a string; it
reads the URL slice's elements, which the precondition owns (a fraction or read-only). -/
axiom fmt.SprintfAttrs.wp_proof : fmt.SprintfAttrs.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
