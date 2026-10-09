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

/-- `(*node[T]).mutableChild(i)`: make child `i` (at `p`) owned (`mutableFor`), store it
back in the child slice, and return it. Stated on the node's own memory and the one
child, so that it can be called on two children in turn (stealing). -/
abbrev node.mutableChild.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (is : List (V × K)) (ps : List Loc)
    (i : w64) (p : Loc) (t : Tree (V × K)),
  0 ≤ sint.Z i → ps[sint.nat i]? = some p →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ nodeShallow (V := V) c (DFrac.own 1) n is ps ∗
      ownNode o c f less (DFrac.own 1) p t }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"mutableChild")) (Val #i))
  {{ (c' : Loc), RET #c';
      nodeShallow (V := V) c (DFrac.own 1) n is (ps.set (sint.nat i) c') ∗
      ownedNode o c f less (DFrac.own 1) c' t }}

end spec

end btree
end EtcdGrove
end Perennial
