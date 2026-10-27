/-
`(*metav1.Time).Equal(u)` (`time.go`): of non-nil times, some `bool`. Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.apis.«meta».v1
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metav1

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

/-- `t.Equal(u)` of two non-nil times: some `bool` (`time.Time.Equal`'s spec in Perennial). -/
abbrev Time.Equal.spec : Prop :=
  ∀ (a b : Loc) (ta tb : k8s_io.apimachinery.pkg.apis.«meta».v1.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ a ↦ ta ∗ b ↦ tb }}
    (App (Val (a @!! go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Time.ty @!! go!"Equal")) (Val #b))
  {{ (eq : Bool), RET #eq; a ↦ ta ∗ b ↦ tb }}

end spec

end metav1
end EtcdGrove
end Perennial
