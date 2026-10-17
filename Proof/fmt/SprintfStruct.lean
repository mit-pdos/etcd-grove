/-
The trust boundary of `Spec/fmt/SprintfStruct.lean` (etcd-io/etcd#22527, branch
`pr-verify/etcd-22527`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfStruct

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **The trust boundary**: `fmt.Sprintf` with one `membership.Attributes` argument whose
`ClientURLs` the caller can read returns some string, and gives the arguments' slice back.

True of Go: `fmt.(*pp).printArg` calls `handleMethods` only on a value implementing `Formatter`,
`Stringer` or `error` (`Attributes` has no methods), and formats a struct by reflection, field by
field (`printValue`), each field again through `handleMethods` (a `string`, a `[]string`: no
methods); it reads the `Name` string and the `ClientURLs` slice's backing array (the precondition's
`↦*□`: read-only, so no write races the read) and the strings in it, and nothing else, and does not
panic. True of Perennial's model of `Sprintf` (`Perennial/TrustedCode/fmt.lean`) as well, which
formats an argument of a type it does not know as an unknown directive and reads only the
arguments' slice. -/
axiom fmt.SprintfStruct.wp_proof : fmt.SprintfStruct.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
