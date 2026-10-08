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

/-- `(*FreeListG[T]).freeNode(n)`: keep `n` if there is room; whether it was kept. -/
abbrev FreeListG.freeNode.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] (f n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.google.btree ∗ isFreeList (V := V) f ∗ freeNode (V := V) n }}
    (App (Val (f @!! go.GoType.PointerType (FreeListG.ty T) @!! go!"freeNode")) (Val #n))
  {{ (out : Bool), RET #out; True }}

end spec

end Btree
end EtcdGrove
end Perennial
