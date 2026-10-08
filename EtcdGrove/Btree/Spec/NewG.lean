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

/-- `NewG[T](degree, less)`: an empty tree (with a free list of its own). -/
abbrev NewG.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (degree : w64) (less : GoFunc),
  1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isLess o less }}
    (App (App (Val #(functions NewG [T])) (Val #degree)) (Val #less))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end Btree
end EtcdGrove
end Perennial
