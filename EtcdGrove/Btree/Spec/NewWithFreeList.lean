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

/-- `NewWithFreeList(degree, f)`: an empty `BTree` using the free list `f`. -/
abbrev NewWithFreeList.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (degree : w64) (f : Loc),
  1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isItemOrderLess o ∗ isFreeList (V := GoInterface) f }}
    (App (App (Val #(functions NewWithFreeList [])) (Val #degree)) (Val #f))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end Btree
end EtcdGrove
end Perennial
