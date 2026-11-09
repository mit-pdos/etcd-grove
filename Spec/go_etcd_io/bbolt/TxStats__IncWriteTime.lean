/-
`tx.stats.IncWriteTime` (`tx.go`): an atomic counter of the transaction's statistics (`atomic.AddInt64`/`LoadInt64`), any fraction.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) some new value. -/
def TxStats.IncWriteTime.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (d : w64),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (Val ((structFieldRef go_etcd_io.bbolt.Tx go!"stats" tx) @!! go.GoType.PointerType TxStats.ty @!! go!"IncWriteTime")) (Val #d))
  {{ (n : w64), RET #n; boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
