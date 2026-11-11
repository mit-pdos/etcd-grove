/-
The trust boundary: `fmt.Errorf` of `pre ++ "%w"` over one error (`Spec/fmt/ErrorfWrap.lean`).
-/
module

public import Spec.fmt.ErrorfWrap

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **Trust boundary** (errorf-wrap, 2026-11-06): Go's `fmt.Errorf` (`fmt/errors.go:34-81`) formats
`pre ++ "%w"` (`pre` copied verbatim, having no `%`; `%w` as `%v` of `inner`, its `Error()`) and,
with exactly one `%w`, returns `&wrapError{msg: s, err: inner}`, whose methods are `Error()`
(`return e.msg`) and `Unwrap()` (`return e.err`): the right side of the post. The left side is
Perennial's model (`errors.New(format)`, whose `Error()` returns `format = pre ++ "%w"`), so that
the axiom contradicts no proof that steps into the model; both sides give the message's prefix
`pre` (N1a, k8s etcd3 7c-2 part 2, 2026-11-06). Only reads the arguments' slice (`a[i].(error)` copies the value). Checked in Go:
`notes/axiom-review/errorf-wrap.md` (survives). -/
axiom fmt.ErrorfWrap.wp_proof : fmt.ErrorfWrap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
