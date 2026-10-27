/-
`listers.NewNamespaced[T](parent, namespace)` (`generic_helpers.go:43`): the lister value `parent`
restricted to `namespace`. Lean-first.
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

/-- **`NewNamespaced[T](p, ns)`** returns `p` with namespace `ns`. -/
abbrev NewNamespaced.spec : Prop :=
  ∀ (X : go.GoType) (p : ResourceIndexer Loc) (ns : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers }}
    (App (App (Val #(functions NewNamespaced [go.GoType.PointerType X])) (Val #p)) (Val #ns))
  {{ RET #({ p with namespace' := ns } : ResourceIndexer Loc); True }}

end spec

end listers
end EtcdGrove
end Perennial
