/-
`(*storeIndex).deleteKeyFromIndex(key, indexValue, index)` (`thread_safe_store.go:241`): the key
removed from the value's set, which is dropped once empty. Lean-first.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `i.deleteKeyFromIndex(key, v, l)`: `key` not in `v`'s set of the index `l` (the receiver is
unused). -/
abbrev storeIndex.deleteKeyFromIndex.spec : Prop :=
  ∀ (i l : Loc) (X : IxN) (key v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ ownIxN l (DFrac.own 1) X }}
    (App (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"deleteKeyFromIndex"))
      (Val #key)) (Val #v)) (Val #l))
  {{ RET #(); ∃ X' : IxN, ownIxN l (DFrac.own 1) X' ∗
      ⌜viewN X' = fun w => if w = v then GMap.delete key (viewN X w) else viewN X w⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
