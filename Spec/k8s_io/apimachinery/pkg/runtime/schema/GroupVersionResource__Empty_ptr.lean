/-
`(*schema.GroupVersionResource).Empty()`: the trust boundary (apimachinery's `runtime/schema` is translated types and names only). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the informers' FIFO, whose
slow-queue trace calls it).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.runtime.schema

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.schema.Assumptions]

/-- `(&gvr).Empty()` of a variable `l ↦{dq} gvr`: some `bool`; the variable is unchanged. -/
abbrev schema.GroupVersionResource.Empty_ptr.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (gvr : k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource),
  {{ (l ↦{dq} gvr : IProp GF) }}
    (App (Val (l @!! go.GoType.PointerType
      k8s_io.apimachinery.pkg.runtime.schema.GroupVersionResource.ty @!! go!"Empty")) (Val #()))
  {{ (b : Bool), RET #b; l ↦{dq} gvr }}

end spec

end EtcdGrove
end Perennial
