module
public import Proof.go_etcd_io.bbolt.Init

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

/-- `s.GetNodeDeref()`: the counter `NodeDeref`, read atomically. -/
abbrev TxStats.GetNodeDeref.spec : Prop :=
  ∀ (l : Loc) (v : TxStats) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType TxStats.ty @!! go!"GetNodeDeref")) (Val #()))
  {{ RET #v.NodeDeref'; l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
