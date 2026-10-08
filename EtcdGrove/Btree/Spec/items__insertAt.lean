import EtcdGrove.Btree.Defs
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

/-- `(*items[T]).insertAt(index, item)`: `item` goes in at `index`, the rest shifts
right (`append` grows the slice by one, then an overlapping `copy` shifts the tail). -/
abbrev items.insertAt.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T]
    (s : Loc) (sl : GoSlice) (vs : List V) (index : w64) (item : V),
  0 ≤ sint.Z index → sint.Z index ≤ vs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗
      s ↦ sl ∗ sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) }}
    (App (App (Val (s @!! go.GoType.PointerType (items.ty T) @!! go!"insertAt")) (Val #index))
      (Val #item))
  {{ (sl' : GoSlice), RET #();
      s ↦ sl' ∗ sl' ↦* (vs.take (sint.nat index) ++ item :: vs.drop (sint.nat index)) ∗
      ownSliceCap V sl' (DFrac.own 1) }}

end spec

end Btree
end EtcdGrove
end Perennial
