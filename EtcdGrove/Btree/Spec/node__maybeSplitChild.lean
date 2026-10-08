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

/-- `(*node[T]).maybeSplitChild(i, maxItems)`: if child `i` is full (`maxItems` items),
split it at `maxItems / 2`, the middle item moving up to `i`; whether it did. -/
abbrev node.maybeSplitChild.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (n : Loc) (is : List (V × K))
    (cs : List (Tree (V × K))) (i maxItems : w64) (cis : List (V × K))
    (ccs : List (Tree (V × K))),
  0 ≤ sint.Z i → sint.nat i ≤ is.length → cs[sint.nat i]? = some (.node cis ccs) →
  (ccs = [] ∨ ccs.length = cis.length + 1) → 0 < sint.Z maxItems →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isCow o c f less ∗ ownedNode o c f less (DFrac.own 1) n (.node is cs) }}
    (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"maybeSplitChild")) (Val #i)) (Val #maxItems))
  {{ (b : Bool), RET #b;
      if cis.length < sint.nat maxItems then
        ⌜b = false⌝ ∗ ownedNode o c f less (DFrac.own 1) n (.node is cs)
      else
        ⌜b = true⌝ ∗ ∃ e : V × K, ⌜cis[sint.nat maxItems / 2]? = some e⌝ ∗
        ownedNode o c f less (DFrac.own 1) n
          (.node (is.take (sint.nat i) ++ e :: is.drop (sint.nat i))
            (cs.take (sint.nat i) ++
              .node (cis.take (sint.nat maxItems / 2)) (ccs.take (sint.nat maxItems / 2 + 1)) ::
              .node (cis.drop (sint.nat maxItems / 2 + 1)) (ccs.drop (sint.nat maxItems / 2 + 1)) ::
              cs.drop (sint.nat i + 1))) }}

end spec

end Btree
end EtcdGrove
end Perennial
