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

/-- `NewFreeList(size)`: an empty free list for `BTree`s. -/
abbrev NewFreeList.spec : Prop :=
  ∀ (size : w64), 0 ≤ sint.Z size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree }}
    (App (Val #(functions NewFreeList [])) (Val #size))
  {{ (f : Loc), RET #f; isFreeList (GF := GF) (V := GoInterface) f }}

end spec

end Btree
end EtcdGrove
end Perennial
