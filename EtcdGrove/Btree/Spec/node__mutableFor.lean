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

/-- `(*node[T]).mutableFor(cow)`: the node itself if the tree (context `cow`) owns it,
else a fresh owned copy (items and child pointers copied, the children shared). -/
abbrev node.mutableFor.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗ ownNode o c f less (DFrac.own 1) n t }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"mutableFor")) (Val #c))
  {{ (n' : Loc), RET #n'; ownedNode o c f less (DFrac.own 1) n' t }}

end spec

end Btree
end EtcdGrove
end Perennial
