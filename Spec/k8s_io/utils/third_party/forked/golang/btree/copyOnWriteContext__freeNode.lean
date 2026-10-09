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

/-- `(*copyOnWriteContext[T]).freeNode(n)`: give `n` to the free list if the context
owns it (`ftStored`, or `ftFreelistFull` if the list is full); a node it does not own is
left alone (`ftNotOwned`). It touches only `n`'s own memory, so the caller gives up just
that: an owned node's fields and slices (`nodeShallow`; its children may have gone
elsewhere, as in a merge or a root collapse) or a frozen node. -/
abbrev copyOnWriteContext.freeNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗
      ((∃ (is : List (V × K)) (ps : List Loc), nodeShallow (V := V) c (DFrac.own 1) n is ps) ∨
       ∃ t : Tree (V × K), frozen o c f less n t) }}
    (App (Val (c @!! go.GoType.PointerType (copyOnWriteContext.ty T) @!! go!"freeNode"))
      (Val #n))
  {{ (r : w64), RET #r; True }}

end spec

end btree
end EtcdGrove
end Perennial
