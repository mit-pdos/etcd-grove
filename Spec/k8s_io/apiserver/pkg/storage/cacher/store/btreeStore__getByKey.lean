/-
`(*btreeStore).getByKey(key)` (`btree.go`): the element with the key, if any, as an `interface{}`
(holding a nil `*Element` if there is none: the B-tree's `Get` returns the zero value), whether
there is one, and no error; at any fraction. Lean-first (no Rocq counterpart).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev btreeStore.getByKey.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (s : List (Loc × GoString)) (rv : w64) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownStore p dq s rv }}
    (App (Val (p @!! go.GoType.PointerType btreeStore.ty @!! go!"getByKey")) (Val #key))
  {{ RET (PairV (PairV #(interface.mkOk (go.GoType.PointerType Element.ty) #(lookupElem s key))
        #((btree.lookup s key).isSome)) #GoInterface.nil);
      ownStore p dq s rv }}

end spec

end cacher
end EtcdGrove
end Perennial
