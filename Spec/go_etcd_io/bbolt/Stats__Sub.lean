module
public import Proof.go_etcd_io.bbolt.Init
public import Spec.go_etcd_io.bbolt.TxStats__Sub

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

/-- `s.Sub(other)`: `s` if `other` is nil, else the freelist counts of `s`, the
difference of the transaction counts and statistics, no open transactions. -/
abbrev Stats.Sub.spec : Prop :=
  ∀ (l o : Loc) (v w : Stats) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ l ↦{dq1} v ∗ (if o = null then True else o ↦{dq2} w) }}
    (App (Val (l @!! go.GoType.PointerType Stats.ty @!! go!"Sub")) (Val #o))
  {{ (r : Stats), RET #r; ⌜r = if o = null then v else Stats.mk (TxStats.subAll v.TxStats' w.TxStats') v.FreePageN' v.PendingPageN' v.FreeAlloc' v.FreelistInuse' (v.TxN' - w.TxN') (W64 0)⌝ ∗
      l ↦{dq1} v ∗ (if o = null then True else o ↦{dq2} w) }}

end spec

end bbolt
end EtcdGrove
end Perennial
