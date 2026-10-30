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

/-- `n.minKeys()`: 1 for a leaf, 2 for a branch. -/
abbrev node.minKeys.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dq} nv }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"minKeys")) (Val #()))
  {{ RET #(if nv.isLeaf' then W64 1 else W64 2); nl ↦{dq} nv }}

end spec

end bbolt
end EtcdGrove
end Perennial
