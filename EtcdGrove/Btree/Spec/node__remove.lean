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

/-- `(*node[T]).remove(item, minItems, typ)` from an owned subtree whose children may
be grown before descending: the item with `item`'s key, the smallest or the largest
(`tgt`) is removed and returned. The node loses at most one item, and none if the child
it descends into (`remIdx`) has more than `minItems` (so a parent that made sure of that
keeps its shape).

The node needs an item to remove when it is a leaf (except by key), and, when
internal, either an item or a first child that need not grow (the root after a merge
left it without items). -/
abbrev node.remove.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)) (item : V)
    (tgt : Target K) (minItems typ : w64) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems → t.items.length ≤ 2 * d - 1 →
  sint.Z minItems = d - 1 → 2 ≤ d → d ≤ 2 ^ 62 → typ = tgt.code →
  (h = 0 → tgt.code ≠ W64 0 → 1 ≤ t.items.length) →
  (0 < h → 1 ≤ t.items.length ∨ ∃ c0, t.children[0]? = some c0 ∧ d ≤ c0.items.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n t ∗
      targetItem o tgt item ∗ allItems o t.elems }}
    (App (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"remove")) (Val #item)) (Val #minItems)) (Val #typ))
  
  {{ (out : V) (found : Bool), RET (PairV #out #found);
      ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
      ⌜t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
        out = ((removeOp tgt t.elems).2).getD (zero_val V) ∧
        found = ((removeOp tgt t.elems).2).isSome ∧
        t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1 ∧
        (0 < h → (∃ c1, t.children[remIdx o.lt tgt t.items]? = some c1 ∧ d ≤ c1.items.length) →
          t'.items.length = t.items.length)⌝ }}

end spec

end Btree
end EtcdGrove
end Perennial
