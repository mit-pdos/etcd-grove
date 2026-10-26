/-
`(*btreeStore).Clone()` (`k8s.io/apiserver/pkg/storage/cacher/store/btree.go`): a new store with
the same entries and resource version, its tree a `Clone` of the store's (after it, the two are
separate resources). Lean-first (no Rocq counterpart).
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
abbrev btreeStore.Clone.spec : Prop :=
  ∀ (p : Loc) (s : List (Loc × GoString)) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗
      ownStore p (DFrac.own 1) s rv }}
    (App (Val (p @!! go.GoType.PointerType btreeStore.ty @!! go!"Clone")) (Val #()))
  {{ (p2 : Loc), RET #p2; ownStore p (DFrac.own 1) s rv ∗ ownStore p2 (DFrac.own 1) s rv }}

end spec

end cacher
end EtcdGrove
end Perennial
