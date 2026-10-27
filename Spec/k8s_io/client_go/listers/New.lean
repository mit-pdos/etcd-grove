/-
`listers.New[T](indexer, resource)` (`generic_helpers.go:38`): the lister value over `indexer`, not
namespaced. Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI k8s_io.client_go.listers

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

/-- **`New[T](idx, res)`** returns `ResourceIndexer[T]{indexer: idx, resource: res}`. -/
abbrev New.spec : Prop :=
  ∀ (X : go.GoType) (idx : GoInterface) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers }}
    (App (App (Val #(functions New [go.GoType.PointerType X])) (Val #idx)) (Val #res))
  {{ RET #(⟨idx, res, []⟩ : ResourceIndexer Loc); True }}

end spec

end listers
end EtcdGrove
end Perennial
