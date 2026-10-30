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

/-- `n.splitIndex(thr)`: the index at which to split the node's inodes so that the first page
fills `thr`, and that page's size (`splitIndexOf`). -/
abbrev node.splitIndex.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (dq : DFrac) (ins : List internal.common.Inode) (dqs : DFrac) (thr : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"splitIndex")) (Val #thr))
  {{ RET (PairV #(splitIndexOf thr ins).1 #(splitIndexOf thr ins).2);
      nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins }}

end spec

end bbolt
end EtcdGrove
end Perennial
