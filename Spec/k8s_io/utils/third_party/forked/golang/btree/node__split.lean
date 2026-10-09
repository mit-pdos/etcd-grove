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

/-- `(*node[T]).split(i)`: the node keeps the items before `i` (and their children);
item `i` is returned, with a new node holding the items after it (and their children). -/
abbrev node.split.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (is : List (V × K))
    (cs : List (Tree (V × K))) (i : w64) (e : V × K),
  0 ≤ sint.Z i → is[sint.nat i]? = some e → (cs = [] ∨ cs.length = is.length + 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n (.node is cs) }}
    (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"split")) (Val #i))
  {{ (n2 : Loc), RET (PairV #e.1 #n2);
      ownedNode o c f less (DFrac.own 1) n
        (.node (is.take (sint.nat i)) (cs.take (sint.nat i + 1))) ∗
      ownedNode o c f less (DFrac.own 1) n2
        (.node (is.drop (sint.nat i + 1)) (cs.drop (sint.nat i + 1))) }}

end spec

end btree
end EtcdGrove
end Perennial
