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

/-- `n.write(p)` onto an empty page (its header `hdr` has no flags and no elements; the rest of
the page `rest`): the header gets the node's kind and its number of inodes, and the inodes go
onto the page as `WriteInodeToPage` writes them (nothing for no inodes). It panics on a page
that is not empty (`Assert`) and on 65535 inodes or more; and `WriteInodeToPage`'s conditions:
non-empty keys, a layout that fits in the page and below `MaxAllocSize`, no branch inode whose
child is the page itself. -/
abbrev node.write.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (dqn : DFrac) (ins : List internal.common.Inode) (dqs : DFrac)
    (ks vs : List (List w8)) (q : DFrac) (p : Loc) (hdr : internal.common.Page) (rest : List w8),
  p.locCar ≠ 0 → hdr.count' = W16 0 → hdr.flags' = W16 0 → ins.length < 65535 →
  ks.length = ins.length → vs.length = ins.length →
  (∀ i < ins.length, 0 < (ks.getD i []).length) →
  16 + 16 * ins.length + kvLen ks vs ins.length ≤ 2147483647 →
  16 * ins.length + kvLen ks vs ins.length ≤ rest.length →
  (nv.isLeaf' = false → ∀ i < ins.length, (ins.getD i (zero_val internal.common.Inode)).pgid' ≠ hdr.id') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗
      inodeData ins ks vs q ∗ p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) rest }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"write")) (Val #p))
  {{ RET #(); nl ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodeData ins ks vs q ∗
      p ↦ ({ hdr with flags' := (if nv.isLeaf' then W16 2 else W16 1), count' := W16 (ins.length : Int) } : internal.common.Page) ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (writtenElems nv.isLeaf' ks vs ins ++ kvBytes ks vs ++
          rest.drop (16 * ins.length + kvLen ks vs ins.length)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
