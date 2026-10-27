/-
`(*storeIndex).addKeyToIndex(key, indexValue, index)` (`thread_safe_store.go:232`): the key added
to the value's set, which is made if the value has none. Lean-first.
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

/-- `i.addKeyToIndex(key, v, l)`: `key` in `v`'s set of the index `l` (the receiver is unused). -/
abbrev storeIndex.addKeyToIndex.spec : Prop :=
  ∀ (i l : Loc) (X : IxN) (key v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ ownIxN l (DFrac.own 1) X }}
    (App (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"addKeyToIndex"))
      (Val #key)) (Val #v)) (Val #l))
  {{ RET #(); ∃ X' : IxN, ownIxN l (DFrac.own 1) X' ∗
      ⌜viewN X' = fun w => if w = v then <[key := sets.present]> (viewN X w) else viewN X w⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
