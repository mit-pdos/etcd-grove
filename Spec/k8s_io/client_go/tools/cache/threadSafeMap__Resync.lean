/-
`(*threadSafeMap).Resync()` (`thread_safe_store.go:524`): nothing to do. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

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

/-- `c.Resync()`: no error, nothing changed. -/
abbrev threadSafeMap.Resync.spec : Prop :=
  ∀ (c : Loc),
  {{ (True : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Resync")) (Val #()))
  {{ RET #interface.nil; True }}

end spec

end cache
end EtcdGrove
end Perennial
