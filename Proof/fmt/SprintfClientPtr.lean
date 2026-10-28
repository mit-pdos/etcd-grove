/-
Proof of `Spec/fmt/SprintfClientPtr.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.SprintfClientPtr

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

/-- **Trust boundary** (item 5): Go's `fmt.Sprintf` formats a `*clientv3.Client` by its kind
(it implements none of `Formatter`, `Stringer`, `error`, `GoStringer`), calling nothing; the
model of `Sprintf` (`Perennial/TrustedCode/fmt.lean`) describes the output up to the first
directive it does not interpret, as for any argument. -/
axiom fmt.SprintfClientPtr.wp_proof : fmt.SprintfClientPtr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
