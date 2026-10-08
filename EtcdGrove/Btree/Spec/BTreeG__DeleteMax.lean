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

/-- `(*BTreeG[T]).DeleteMax()`: remove the largest entry. -/
abbrev BTreeG.DeleteMax.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (t : Loc) (s : List (V × K)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ ownBTree o t (DFrac.own 1) s }}
    (App (Val (t @!! go.GoType.PointerType (BTreeG.ty T) @!! go!"DeleteMax")) (Val #()))
  {{ RET (PairV #((removeOp (.max : Target K) s).2.getD (zero_val V)) #((removeOp (.max : Target K) s).2.isSome));
      ownBTree o t (DFrac.own 1) (removeOp (.max : Target K) s).1 }}

end spec

end Btree
end EtcdGrove
end Perennial
