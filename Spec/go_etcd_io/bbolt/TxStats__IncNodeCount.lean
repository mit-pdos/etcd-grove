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

/-- `s.IncNodeCount(delta)`: adds `delta` to the counter `NodeCount` atomically and returns the sum. -/
abbrev TxStats.IncNodeCount.spec : Prop :=
  ∀ (l : Loc) (v : TxStats) (delta : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦ v }}
    (App (Val (l @!! go.GoType.PointerType TxStats.ty @!! go!"IncNodeCount")) (Val #delta))
  {{ (v' : TxStats), RET #(v.NodeCount' + delta);
      ⌜v' = ({ v with NodeCount' := v.NodeCount' + delta } : TxStats)⌝ ∗ l ↦ v' }}

end spec

end bbolt
end EtcdGrove
end Perennial
