/-
The trust boundary: `fmt.Errorf` of a format without `%w` is `errors.New` of its message
(`Spec/fmt/ErrorfPlain.lean`).
-/
module

public import Spec.fmt.ErrorfPlain

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
/-- **Trust boundary** (rafthttp stage 5e-3): `fmt.Errorf` (`fmt/errors.go`) formats its
arguments as `Sprintf` does (calling the `Error()`/`String()` methods `fmt.argsOk` gives) and,
with no `%w` verb, returns `errors.New(s)`. -/
axiom fmt.ErrorfPlain.wp_proof : fmt.ErrorfPlain.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
