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

/-- `NewFreeListG[T](size)`: an empty free list holding up to `size` nodes (`make` needs
`0 ≤ size`). -/
abbrev NewFreeListG.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (size : w64),
  0 ≤ sint.Z size →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree }}
    (App (Val #(functions NewFreeListG [T])) (Val #size))
  {{ (f : Loc), RET #f; isFreeList (V := V) f }}

end spec

end Btree
end EtcdGrove
end Perennial
