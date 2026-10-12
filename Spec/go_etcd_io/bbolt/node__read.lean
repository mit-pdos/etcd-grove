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

/-- `n.read(p)` of a page that `ReadInodeFromPage` reads (its bytes `pg` at `l`): the node
takes the page's id, kind and inodes (a new slice `s` of `inodesOf l pg`, their keys and values
pointing into the page), and its key is the first inode's (nil for an empty page). -/
abbrev node.read.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (l : Loc) (q : DFrac) (pg : List w8),
  l.locCar ≠ 0 → pageReadable pg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ bytesPointsto l q pg }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"read")) (Val #l))
  {{ (s : GoSlice), RET #();
      nl ↦ ({ nv with pgid' := W64 (pageId pg), isLeaf' := decide (pageFlags pg = leafPageFlag), inodes' := s, key' := (if pageCount pg = 0 then slice.nil else (inodeOf l pg 0).key') } : node) ∗
      s ↦* inodesOf l pg ∗ ownSliceCap internal.common.Inode s (DFrac.own 1) ∗
      bytesPointsto l q pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
