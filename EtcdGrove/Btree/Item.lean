/-
The non-generic API (`BTree`, the B-tree of `Item` interface values ordered by their
`Less` methods): what it needs of the items.
-/
import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Init

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI github_com.google.btree

section item
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]
variable {K : Type}

/-- The items' `Less` methods decide the order: `a.Less(b)` (dispatched on the
interface value `a`) on items with keys `ka`, `kb` returns whether `ka < kb`. -/
def isItemOrderLess (o : ItemOrder GF GoInterface K) : IProp GF :=
  iprop(□ ∀ (a b : GoInterface) (ka kb : K),
    {{ o.item a ka ∗ o.item b kb }}
      (App (App (Val (GoInstruction (MethodResolve Item.ty go!"Less"))) (Val #a)) (Val #b))
    {{ (r : Bool), RET #r; ⌜r = true ↔ o.lt ka kb⌝ }})

instance isItemOrderLess_persistent (o : ItemOrder GF GoInterface K) :
    Persistent (isItemOrderLess o) := by
  unfold isItemOrderLess; infer_instance

end item

section int
variable {GF : BundledGFunctors} [FfiSyntax] [GoGlobalContext]

/-- `btree.Int` items (`Int` values in an `Item`), ordered as `int`s. -/
def intOrder : ItemOrder GF GoInterface w64 where
  lt a b := sint.Z a < sint.Z b
  order := ⟨fun _ => Int.lt_irrefl _, fun _ _ _ => Int.lt_trans, fun a b => by
    rcases Int.lt_trichotomy (sint.Z a) (sint.Z b) with h | h | h
    · exact .inl h
    · exact .inr (.inl (BitVec.eq_of_toInt_eq h))
    · exact .inr (.inr h)⟩
  item v k := iprop(⌜v = interface.mkOk Int'.ty #k⌝)
  item_persistent _ _ := by infer_instance

end int

end Btree
end EtcdGrove
end Perennial
