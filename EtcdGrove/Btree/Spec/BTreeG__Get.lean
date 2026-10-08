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

/-- `(*BTreeG[T]).Get(key)`: the item with `key`'s key, if any (at any fraction). -/
abbrev BTreeG.Get.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (dq : DFrac) (s : List (V × K)) (key : V) (k : K),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t dq s ∗ o.item key k }}
    (App (Val (t @!! go.GoType.PointerType (BTreeG.ty T) @!! go!"Get")) (Val #key))
  {{ RET (PairV #((lookup s k).getD (zero_val V)) #((lookup s k).isSome)); ownBTree o t dq s }}

end spec

end Btree
end EtcdGrove
end Perennial
