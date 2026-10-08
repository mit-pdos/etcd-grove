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

/-- `NewWithFreeListG[T](degree, less, f)`: an empty tree using the free list `f`.
`degree <= 1` panics; above `2^62`, `maxItems()` overflows. -/
abbrev NewWithFreeListG.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (degree : w64) (less : GoFunc) (f : Loc),
  1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isLess o less ∗ isFreeList (V := V) f }}
    (App (App (App (Val #(functions NewWithFreeListG [T])) (Val #degree)) (Val #less)) (Val #f))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end Btree
end EtcdGrove
end Perennial
