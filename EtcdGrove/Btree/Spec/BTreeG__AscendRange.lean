import EtcdGrove.Btree.Defs
import EtcdGrove.Btree.Model
import EtcdGrove.Btree.Init

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

/-- `(*BTreeG[T]).AscendRange(...)`: call `iterator` on the entries ascending, from `greaterOrEqual` up to (not including) `lessThan`, until it returns
false (at any fraction of the tree; the iterator keeps its own state in `I`). -/
abbrev BTreeG.AscendRange.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (greaterOrEqual : V) (kge : K) (lessThan : V) (klt : K)
    (iterator : GoFunc) (I : List (V × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s ∗ o.item greaterOrEqual kge ∗ o.item lessThan klt ∗
      iterProtocol o iterator (ascRange o.lt s (some kge) (some klt)) I ∗ I [] false }}
    (App (App (App (Val (t @!! go.GoType.PointerType (BTreeG.ty T) @!! go!"AscendRange")) (Val #greaterOrEqual)) (Val #lessThan)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (ascRange o.lt s (some kge) (some klt)) I }}

end spec

end Btree
end EtcdGrove
end Perennial
