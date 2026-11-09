/-
`tx.recursivelyCheckPageKeyOrder` (`tx_check.go`): part of `Tx.Check`, which reports every inconsistency of a well-formed file as none (run by `Commit`'s error path's `freepages` under `NoFreelistSync`, on the spare reader slot).
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

/-- (internal) the walk returns, reporting nothing on a well-formed tree; its maps and channel are the caller's (`chanRes`). -/
def Tx.recursivelyCheckPageKeyOrder.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (m1 : val) (m2 : val) (m3 : val),
  {{ boltTx (GF := GF) tx γ q T }}
    (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"recursivelyCheckPageKeyOrder")) (Val m1)) (Val m2)) (Val m3))
  {{ RET #(); boltTx tx γ q T }}

end spec

end Bbolt
end EtcdGrove
end Perennial
