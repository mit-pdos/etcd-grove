/-
`(*btreeStore).ResourceVersion()` (`btree.go`): the store's resource version (at any fraction). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.store.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.store

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev btreeStore.ResourceVersion.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (s : List (Loc × GoString)) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownStore p dq s rv }}
    (App (Val (p @!! go.GoType.PointerType btreeStore.ty @!! go!"ResourceVersion")) (Val #()))
  {{ RET #rv; ownStore p dq s rv }}

end spec

end cacher
end EtcdGrove
end Perennial
