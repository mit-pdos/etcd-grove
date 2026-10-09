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

/-- `(*items[T]).pop()`: the last item is returned and removed. -/
abbrev items.pop.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T]
    (s : Loc) (sl : GoSlice) (vs : List V) (v : V),
  vs.getLast? = some v →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      s ↦ sl ∗ sl ↦* vs ∗ ownSliceCap V sl (DFrac.own 1) }}
    (App (Val (s @!! go.GoType.PointerType (items.ty T) @!! go!"pop")) (Val #()))
  {{ (sl' : GoSlice), RET #v;
      s ↦ sl' ∗ sl' ↦* vs.dropLast ∗ ownSliceCap V sl' (DFrac.own 1) }}

end spec

end btree
end EtcdGrove
end Perennial
