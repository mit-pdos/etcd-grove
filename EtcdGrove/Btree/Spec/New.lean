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

/-- `New(degree)`: an empty `BTree` of `Item`s, ordered by their `Less` methods. -/
abbrev New.spec : Prop :=
  ∀ {K : Type} (o : ItemOrder GF GoInterface K) (degree : w64),
  1 < sint.Z degree → sint.Z degree ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isItemOrderLess o }}
    (App (Val #(functions New [])) (Val #degree))
  {{ (t : Loc), RET #t; ownBTree o t (DFrac.own 1) [] }}

end spec

end Btree
end EtcdGrove
end Perennial
