/-
`(*concurrency.stm).commit` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: the conflicts closure (`readSet.cmps.spec` or none), `writeSet.puts.spec`; the KV
contract's `Txn(...).If(cmps...).Then(puts...).Commit()`: with writes, an exclusive update built
from the lent permission (`P` given up, back at the commit): a succeeded step is the writes applied at `σ` (`applied`) with every
comparison true there (each read key at its read mod revision: `readsAgree` at `σ`, with
`etcdLb_init` for the absent ones and W0's history for the present ones), a failed one or an
error no change; without writes, a read-only transaction (serializable if empty: answered at a
view, `RepeatableReads`' stale case of `stmCommitted`) with the persistent read update. An error:
`panic(stmError{err})`.

Changes: from `specs-ref`'s `stm__commit.lean`: restated over `stmCoreAt` and the `Attempt` model.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.commit()` (`RepeatableReads`, `ReadCommitted`): `nil` if a comparison failed, else the committed attempt's reply; or the abort. -/
def stm.commit.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt) (gs : List (OpM → OpM)) (T : State → State → Prop) (P : IProp GF) (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmCoreAt p γ who iso a gs ∗ etcdLent γ T P ∗ P ∗ etcdLb γ σ0 ∗
      ⌜effIn (fun σ σ' => σ' = σ ∨ stmCommitted iso a σ σ') T⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stm.ty @!! go!"commit")) (Val #()))
  {{ (r : val), RET r; stmRet r (fun resp : Loc => iprop(stmCoreStale p γ who iso gs ∗
      P ∗ (⌜resp = null⌝ ∨ ∃ (σ σ' : State) (m : TxnRespM), etcdLb γ σ ∗ etcdLb γ σ' ∗
          ⌜Reach σ0 σ ∧ stmCommitted iso a σ σ' ∧ m.succeeded = true⌝ ∗ txnRespOwn resp (DFrac.own 1) m))) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
