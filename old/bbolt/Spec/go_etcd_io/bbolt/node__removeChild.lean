module
public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.removeChild(target)`: the first occurrence of `target` among the node's children is
removed (in place: the children become `children[:len-1]`); nothing changes if it is not one. -/
abbrev node.removeChild.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (cs : List Loc) (tl : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.children' ↦* cs ∗
      ownSliceCap Loc nv.children' (DFrac.own 1) }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"removeChild")) (Val #tl))
  {{ RET #();
      if decide (tl ∈ cs) then
        nl ↦ ({ nv with children' := slice.slice nv.children' Loc (W64 0) (nv.children'.len - W64 1) } : node) ∗
        slice.slice nv.children' Loc (W64 0) (nv.children'.len - W64 1) ↦* cs.eraseIdx (cs.idxOf tl) ∗
        ownSliceCap Loc (slice.slice nv.children' Loc (W64 0) (nv.children'.len - W64 1)) (DFrac.own 1)
      else
        nl ↦ nv ∗ nv.children' ↦* cs ∗ ownSliceCap Loc nv.children' (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
