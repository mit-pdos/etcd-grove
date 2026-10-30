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

/-- Every counter of `v` minus `w`'s. -/
def TxStats.subAll (v w : TxStats) : TxStats :=
  TxStats.mk (v.PageCount' - w.PageCount') (v.PageAlloc' - w.PageAlloc') (v.CursorCount' - w.CursorCount') (v.NodeCount' - w.NodeCount') (v.NodeDeref' - w.NodeDeref') (v.Rebalance' - w.Rebalance') (v.RebalanceTime' - w.RebalanceTime') (v.Split' - w.Split') (v.Spill' - w.Spill') (v.SpillTime' - w.SpillTime') (v.Write' - w.Write') (v.WriteTime' - w.WriteTime')

/-- `s.Sub(other)`: the difference of the two statistics, counter by counter. -/
abbrev TxStats.Sub.spec : Prop :=
  ∀ (l o : Loc) (v w : TxStats) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦{dq1} v ∗ o ↦{dq2} w }}
    (App (Val (l @!! go.GoType.PointerType TxStats.ty @!! go!"Sub")) (Val #o))
  {{ (d : TxStats), RET #d; ⌜d = TxStats.subAll v w⌝ ∗ l ↦{dq1} v ∗ o ↦{dq2} w }}

end spec

end bbolt
end EtcdGrove
end Perennial
