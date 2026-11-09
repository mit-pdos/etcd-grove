/-
`(*concurrency.stmSerializable).commit` (`client/v3/concurrency/stm.go`), internal: the STM's method.

Users: the user's closure through `STM` (`stmAt_methods`), `runSTM`, `stmSerializable`'s methods.

Proof sketch: `stmSerializable.gets.spec`, the conflicts closure (`readSet.cmps.spec`, and at
`SerializableSnapshot` `readSet.first.spec`, `writeSet.cmps.spec` at `first() + 1`),
`writeSet.puts.spec`; the KV contract's transaction with `Else(gets...)` (with writes: an
exclusive update from `etcdPerm γ T`, a succeeded step `stmCommitted` as in `stm.commit`, and at
`SerializableSnapshot` the written keys' mod revisions at most every read's header; without
writes, read-only, linearizable unless empty); failed: the else-branch's ranges (`respReads`, at
`σ`) added to the read set (`readSet.add.spec`) and kept as the prefetch, the gets' options
cleared. An error: `panic(stmError{err})`.

Changes: from `specs-ref`'s `stmSerializable__commit.lean`: restated over `stmSerAt` and the `Attempt` model.

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

/-- `s.commit()` (serializable levels): `nil` if a comparison failed (the else-branch's reads become the next attempt's prefetched ones), else the committed attempt's reply; or the abort. -/
def stmSerializable.commit.spec : Prop :=
  ∀ (p : Loc) (γ : Cluster) (who : Principal) (iso : w64) (a : Attempt) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmSerAt p γ who iso a ∗ etcdPerm γ T ∗
      ⌜effIn (fun σ σ' => σ' = σ ∨ stmCommitted iso a σ σ') T⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.stmSerializable.ty @!! go!"commit")) (Val #()))
  {{ (r : val), RET r; stmRet r (fun resp : Loc => iprop(stmSerStale p γ who iso ∗
      (⌜resp = null⌝ ∨ ∃ (σ σ' : State) (m : TxnRespM), etcdLb γ σ ∗ etcdLb γ σ' ∗
          ⌜stmCommitted iso a σ σ' ∧ m.succeeded = true⌝ ∗ txnRespOwn resp (DFrac.own 1) m))) iprop(True) }}

end spec

end Concurrency
end EtcdGrove
end Perennial
