module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*BTree[T]).minItems()`: `degree - 1`. -/
abbrev BTree.minItems.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (t : Loc) (dq : DFrac) (tv : BTree V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ t ↦{dq} tv }}
    (App (Val (t @!! go.GoType.PointerType (BTree.ty T) @!! go!"minItems")) (Val #()))
  {{ RET #(tv.degree' - W64 1); t ↦{dq} tv }}

end spec

end btree
end EtcdGrove
end Perennial
