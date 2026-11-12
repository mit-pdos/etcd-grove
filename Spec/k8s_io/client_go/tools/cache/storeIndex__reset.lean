/-
`(*storeIndex).reset()` (`thread_safe_store.go:101`): new, empty indices. Lean-first.
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

/-- `i.reset()`: the indices field holds new, empty indices. -/
abbrev storeIndex.reset.spec : Prop :=
  ∀ (i ip : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indices" i ↦ ip }}
    (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ∃ ip' : Loc, structFieldRef storeIndex go!"indices" i ↦ ip' ∗
      ownIx ip' (DFrac.own 1) ∅ }}

end spec

end cache
end EtcdGrove
end Perennial
