import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init
import EtcdGrove.Btree.Item

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

/-- `(*node[T]).get(key)`: the item with `key`'s key in the subtree (owned or frozen,
at any fraction). -/
abbrev node.get.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K))
    (key : V) (k : K) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗ ownNode o c f less dq n t ∗
      o.item key k ∗ allItems o t.elems }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"get")) (Val #key))
  {{ RET (PairV #((lookup t.elems k).getD (zero_val V)) #((lookup t.elems k).isSome));
      ownNode o c f less dq n t }}

end spec

end Btree
end EtcdGrove
end Perennial
