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

/-- `(*node[T]).insert(item, maxItems)` into a subtree that is not full: `item` replaces
the entry with its key, or is added; the replaced item is returned. Splitting full
children on the way down keeps the shape, and the node gains at most one item. -/
abbrev node.insert.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)) (item : V) (k : K)
    (maxItems : w64) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems → t.items.length < 2 * d - 1 →
  sint.Z maxItems = 2 * d - 1 → 2 ≤ d → d ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n t ∗
      o.item item k ∗ allItems o t.elems }}
    (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"insert")) (Val #item)) (Val #maxItems))
  {{ (old : V) (found : Bool), RET (PairV #old #found);
      ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
      ⌜t'.Shape d h ∧ t'.elems = insert o.lt t.elems (item, k) ∧
        t.items.length ≤ t'.items.length ∧ t'.items.length ≤ t.items.length + 1 ∧
        old = (lookup t.elems k).getD (zero_val V) ∧ found = (lookup t.elems k).isSome⌝ }}

end spec

end btree
end EtcdGrove
end Perennial
