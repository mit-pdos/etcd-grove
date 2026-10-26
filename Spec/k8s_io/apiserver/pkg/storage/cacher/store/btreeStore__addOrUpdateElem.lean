/-
`(*btreeStore).addOrUpdateElem(elem, rv)` (`btree.go`): the element replaces the one with its key,
or is added; the store is at `rv`; the previous element (`nil` if none) is returned. Lean-first (no Rocq counterpart).
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
abbrev btreeStore.addOrUpdateElem.spec : Prop :=
  ∀ (p : Loc) (s : List (Loc × GoString)) (rv0 : w64) (e : Loc) (k : GoString) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownStore p (DFrac.own 1) s rv0 ∗ elemOrder.item e k }}
    (App (App (Val (p @!! go.GoType.PointerType btreeStore.ty @!! go!"addOrUpdateElem")) (Val #e)) (Val #rv))
  {{ RET #(lookupElem s k); ownStore p (DFrac.own 1) (btree.insert go.GoStringLt s (e, k)) rv }}

end spec

end cacher
end EtcdGrove
end Perennial
