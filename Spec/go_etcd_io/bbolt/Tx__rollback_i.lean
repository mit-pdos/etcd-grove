/-
`tx.rollback()` (`tx.go`): a writer's freelist rolled back (unless its meta is already current: kept) and reloaded, then `close`. Users: `Commit`'s error paths, `Rollback`.
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

/-- (internal) the transaction done. -/
def Tx.rollback.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView) (st : CommitStage),
  {{ wtxAt (GF := GF) tx γ T st }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"rollback")) (Val #()))
  {{ RET #(); txDone tx }}

end spec

end Bbolt
end EtcdGrove
end Perennial
