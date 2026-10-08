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

/-- `(*BTreeG[T]).DescendRange(...)`: call `iterator` on the entries descending, from `lessOrEqual` down to (not including) `greaterThan`, until it returns
false (at any fraction of the tree; the iterator keeps its own state in `I`). -/
abbrev BTreeG.DescendRange.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (lessOrEqual : V) (kle : K) (greaterThan : V) (kgt : K)
    (iterator : GoFunc) (I : List (V × K) → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s ∗ o.item lessOrEqual kle ∗ o.item greaterThan kgt ∗
      iterProtocol o iterator (descRange o.lt s (some kle) (some kgt)) I ∗ I [] false }}
    (App (App (App (Val (t @!! go.GoType.PointerType (BTreeG.ty T) @!! go!"DescendRange")) (Val #lessOrEqual)) (Val #greaterThan)) (Val #iterator))
  {{ RET #(); ownBTree o t dq s ∗ iterDone (descRange o.lt s (some kle) (some kgt)) I }}

end spec

end Btree
end EtcdGrove
end Perennial
