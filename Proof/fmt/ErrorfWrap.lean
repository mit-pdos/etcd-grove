/-
The trust boundary: `fmt.Errorf` with one `%s` and one `%w` verb (pr-verify etcd#21714), its
wrapping half (`Spec/fmt/ErrorfWrap.lean`).
-/
module

public import Spec.fmt.ErrorfWrap

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

/-- **The trust boundary**: Go's `fmt.Errorf(format, s, err)` for a format whose verbs are one `%s`
and one `%w` (Go 1.13+, `fmt/errors.go`): it formats the message (calling `err.Error()`, which
returns a string without effects by the premise; `err` is assumed not to be a `fmt.Formatter`, as in
`Spec/fmt/Errorf.lean`: Go would call its `Format` instead, which the premise does not cover) and, the `%w` operand being a non-nil `error`,
returns `&wrapError{msg, err}`, whose `Error()` returns `msg` and whose `Unwrap()` returns `err`;
`*wrapError`'s method set is `{Error, Unwrap}`. It only reads the arguments' slice. -/
axiom fmt.ErrorfWrap.wp_proof : fmt.ErrorfWrap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
