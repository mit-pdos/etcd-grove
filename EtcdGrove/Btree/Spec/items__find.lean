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

/-- `items[T].find(item, less)` on sorted entries: the number of entries with keys below
`item`'s (a `sort.Search`), and whether the entry there has `item`'s key. -/
abbrev items.find.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K)
    (sl : GoSlice) (is : List (V × K)) (dq : DFrac) (item : V) (k : K) (less : GoFunc),
  Sorted o.lt is →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗
      sl ↦*{dq} is.map Prod.fst ∗ isLess o less ∗ o.item item k ∗ allItems o is }}
    (App (App (Val (sl @!! items.ty T @!! go!"find")) (Val #item)) (Val #less))
  {{ (index : w64) (found : Bool), RET (PairV #index #found);
      sl ↦*{dq} is.map Prod.fst ∗
      ⌜sint.nat index = countLt o.lt is k ∧ 0 ≤ sint.Z index ∧
        (found = true ↔ ∃ e, is[sint.nat index]? = some e ∧ e.2 = k)⌝ }}

end spec

end Btree
end EtcdGrove
end Perennial
