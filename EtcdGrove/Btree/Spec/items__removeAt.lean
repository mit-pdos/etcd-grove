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

/-- `(*items[T]).removeAt(index)`: the item at `index` is returned and removed, the rest
shifts left (`copy(s[index:], s[index+1:])`); the vacated last slot goes back to the
capacity. -/
abbrev items.removeAt.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T]
    (s : Loc) (sl : GoSlice) (vs : List V) (index : w64) (v : V),
  0 ≤ sint.Z index → vs[sint.nat index]? = some v →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗
      s ↦ sl ∗ sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) }}
    (App (Val (s @!! go.GoType.PointerType (items.ty T) @!! go!"removeAt")) (Val #index))
  {{ (sl' : GoSlice), RET #v;
      s ↦ sl' ∗ sl' ↦* (vs.take (sint.nat index) ++ vs.drop (sint.nat index + 1)) ∗
      ownSliceCap V sl' (DFrac.own 1) }}

end spec

end Btree
end EtcdGrove
end Perennial
