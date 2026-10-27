/-
`(*storeIndex).updateSingleIndex(name, oldObj, newObj, key)` (`thread_safe_store.go:174`): moves
the key in indexer `name`'s index from its old object's values to its new object's. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreDefs

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

/-- `i.updateSingleIndex(name, old, new, key)` for an indexer `name` (`fv !! name = some f`, with
its function's contract for `F`), on objects that are `nil` or meet `OK`: indexer `name`'s index
updated (`updNPost`; it is made if it had none), the others unchanged. Under the store's write
lock, which holds the indices. -/
abbrev storeIndex.updateSingleIndex.spec : Prop :=
  ∀ (i im ip : Loc) (dqi dqm : DFrac) (fv : GMap GoString GoFunc) (ix : Ix)
    (OK : GoInterface → IProp GF) (F : Fn) (f : GoFunc) (name key : GoString)
    (old new : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗ ⌜fv !! name = some f⌝ ∗
      fnOk OK f F ∗ okNil OK old ∗ okNil OK new ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix }}
    (App (App (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"updateSingleIndex"))
      (Val #name)) (Val #old)) (Val #new)) (Val #key))
  {{ RET #(); ∃ ix' : Ix,
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix' ∗
      ⌜(∀ n, n ≠ name → ix' !! n = ix !! n) ∧
        updNPost F old new key (viewN (ixAt ix name)) (viewN (ixAt ix' name))⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
