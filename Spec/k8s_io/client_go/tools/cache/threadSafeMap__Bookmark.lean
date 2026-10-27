/-
`(*threadSafeMap).Bookmark(rv)` (`thread_safe_store.go:466`): sets the store's resource version,
under the write lock. Lean-first.
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

/-- **`c.Bookmark(rv)`**, logically atomic: the resource version is `rv`, whatever it was
(even `""`). -/
abbrev threadSafeMap.Bookmark.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (rv : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"Bookmark")) (Val #rv))
    @@ ∅
  <<{ storeSt γ (σ.bookmark rv) }>>
  {{ RET #(); True }}

end spec

end cache
end EtcdGrove
end Perennial
