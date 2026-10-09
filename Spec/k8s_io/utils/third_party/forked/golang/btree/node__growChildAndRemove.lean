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

/-- `(*node[T]).growChildAndRemove(i, item, minItems, typ)`: child `i`, the one `remove`
descends into, has only `minItems`; steal an item for it from a sibling, or merge it
with one, then `remove` again (which now descends without growing). -/
abbrev node.growChildAndRemove.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (t : Tree (V × K)) (item : V)
    (tgt : Target K) (i minItems typ : w64) (d h : Nat) (ci : Tree (V × K)),
  t.Shape d h → 0 < h → Sorted o.lt t.elems → t.items.length ≤ 2 * d - 1 →
  1 ≤ t.items.length → sint.Z minItems = d - 1 → 2 ≤ d → d ≤ 2 ^ 62 → typ = tgt.code →
  0 ≤ sint.Z i → sint.nat i = remIdx o.lt tgt t.items →
  t.children[sint.nat i]? = some ci → ci.items.length ≤ d - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n t ∗
      targetItem o tgt item ∗ allItems o t.elems }}
    (App (App (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"growChildAndRemove")) (Val #i)) (Val #item)) (Val #minItems)) (Val #typ))
  
  {{ (out : V) (found : Bool), RET (PairV #out #found);
      ∃ t' : Tree (V × K), ownedNode o c f less (DFrac.own 1) n t' ∗
      ⌜t'.Shape d h ∧ t'.elems = (removeOp tgt t.elems).1 ∧
        out = ((removeOp tgt t.elems).2).getD (zero_val V) ∧
        found = ((removeOp tgt t.elems).2).isSome ∧
        t'.items.length ≤ t.items.length ∧ t.items.length ≤ t'.items.length + 1⌝ }}

end spec

end btree
end EtcdGrove
end Perennial
