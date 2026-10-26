/-
`newBtreeStore(degree)` (`btree.go`): an empty store (a `btreeStore` value) at resource version `0`:
its tree a new B-tree of the given degree ordered by the elements' keys. Lean-first (no Rocq counterpart).
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
abbrev newBtreeStore.spec : Prop :=
  ∀ (degree : w64),
  1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.cacher.store.newBtreeStore)) (Val #degree))
  {{ (t : Loc), RET #(⟨t, 0⟩ : btreeStore); btree.ownBTree elemOrder t (DFrac.own 1) [] }}

end spec

end cacher
end EtcdGrove
end Perennial
