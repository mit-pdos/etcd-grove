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

/-- `(*FreeListG[T]).newNode()`: a node from the free list, or a fresh one. -/
abbrev FreeListG.newNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (f : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isFreeList (V := V) f }}
    (App (Val (f @!! go.GoType.PointerType (FreeListG.ty T) @!! go!"newNode")) (Val #()))
  {{ (n : Loc), RET #n; freeNode (V := V) n }}

end spec

end Btree
end EtcdGrove
end Perennial
