/-
`(*Reflector).rewatchResourceVersion()` (`reflector.go:1135`): the version a re-watch asks for, under the read lock. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (fourth round, the reflector).
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.rewatchResourceVersion()`**: `rewatchRV v u`. -/
abbrev Reflector.rewatchResourceVersion.spec : Prop :=
  ∀ (r : Loc) (v : GoString) (u : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflOwn r v u }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"rewatchResourceVersion")) (Val #()))
  {{ RET #(rewatchRV v u); reflOwn r v u }}

end spec

end cache
end EtcdGrove
end Perennial
