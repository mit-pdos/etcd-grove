/-
`(*Reflector).LastSyncResourceVersion()` (`reflector.go:1099`): the last synced version, under the read lock. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (fourth round, the reflector).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`r.LastSyncResourceVersion()`**: `v`. -/
abbrev Reflector.LastSyncResourceVersion.spec : Prop :=
  ∀ (r : Loc) (v : GoString) (u : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ reflOwn r v u }}
    (App (Val (r @!! go.GoType.PointerType Reflector.ty @!! go!"LastSyncResourceVersion")) (Val #()))
  {{ RET #v; reflOwn r v u }}

end spec

end cache
end EtcdGrove
end Perennial
