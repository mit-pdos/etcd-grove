/-
`(*btreeStore).Replace(objs, rv)` (`btree.go`): the store holds exactly the elements of `objs`
(inserted in order: a later one replaces an earlier one with its key), at `rv`. Lean-first (no Rocq counterpart).
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
abbrev btreeStore.Replace.spec : Prop :=
  ∀ (p : Loc) (s : List (Loc × GoString)) (rv0 : w64) (sl : GoSlice) (dq : DFrac)
    (ents : List (Loc × GoString)) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownStore p (DFrac.own 1) s rv0 ∗ sl ↦*{dq} ents.map Prod.fst ∗
      [∗list] x ∈ ents, elemOrder.item x.1 x.2 }}
    (App (App (Val (p @!! go.GoType.PointerType btreeStore.ty @!! go!"Replace")) (Val #sl)) (Val #rv))
  {{ RET #(); ownStore p (DFrac.own 1) (ents.foldl (btree.insert go.GoStringLt) []) rv ∗
      sl ↦*{dq} ents.map Prod.fst }}

end spec

end cacher
end EtcdGrove
end Perennial
