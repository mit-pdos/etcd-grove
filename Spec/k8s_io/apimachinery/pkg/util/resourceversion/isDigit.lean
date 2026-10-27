/-
`isDigit(b)` (`resourceversion.go`): whether `b` is an ASCII digit. Lean-first.
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.resourceversion.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace resourceversion

open Iris Iris.BI k8s_io.apimachinery.pkg.util.resourceversion

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.resourceversion.Assumptions]

/-- `isDigit(b)`: `'0' ≤ b ≤ '9'`. -/
abbrev isDigit.spec : Prop :=
  ∀ (b : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.resourceversion }}
    (App (Val (@! isDigit)) (Val #b))
  {{ RET #(digitB b); True }}

end spec

end resourceversion
end EtcdGrove
end Perennial
