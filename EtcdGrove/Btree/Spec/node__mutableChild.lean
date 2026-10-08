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

/-- `(*node[T]).mutableChild(i)`: make child `i` owned (`mutableFor`), store it back,
and return it; the node lends it out (`ownedNodeHole`). -/
abbrev node.mutableChild.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (is : List (V × K))
    (cs : List (Tree (V × K))) (i : w64) (t : Tree (V × K)),
  0 ≤ sint.Z i → cs[sint.nat i]? = some t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n (.node is cs) }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"mutableChild")) (Val #i))
  {{ (c' : Loc), RET #c';
      ownedNodeHole o c f less n is cs (sint.nat i) c' ∗
      ownedNode o c f less (DFrac.own 1) c' t }}

end spec

end Btree
end EtcdGrove
end Perennial
