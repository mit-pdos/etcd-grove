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

/-- `n.sizeLessThan(v)`: adding the header and then each inode's element, key and value,
the size stays below `v` (`sizeLessThanFrom`). -/
abbrev node.sizeLessThan.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (dq : DFrac) (ins : List internal.common.Inode) (dqs : DFrac) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"sizeLessThan")) (Val #v))
  {{ RET #(sizeLessThanFrom (W64 16) v (W64 16) ins); nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins }}

end spec

end bbolt
end EtcdGrove
end Perennial
