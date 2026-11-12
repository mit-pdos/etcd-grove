/-
`tx.Stats()` (`tx.go`): a copy of the transaction's statistics (atomic loads).

**Users.** The backend after `Commit` (`batch_tx.go:294-296`: `t.tx.Stats().RebalanceTime`, ...).
Snippet: `ReqBackendBatch`. **Proof sketch.** The statistics live in the `*Tx` until it is
collected; `txDone`/`boltTx` own a read share of them. **Changes.** Unchanged (either a live or a
done transaction). **Margin.** The values are not described.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Api

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

/-- `tx.Stats()`, live or done: some statistics. -/
def Tx.Stats.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (o : Option (Qp × TxView)),
  {{ (match o with
      | none => txDone (GF := GF) tx
      | some (q, T) => boltTx tx γ q T) }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Stats")) (Val #()))
  {{ (s : TxStats), RET #s;
      (match o with
       | none => txDone tx
       | some (q, T) => boltTx tx γ q T) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
