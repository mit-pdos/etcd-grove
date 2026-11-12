/-
`(*txnLeasing).Commit` (`client/v3/leasing/txn.go`).

Users: `leasingKV.Do` (the proxy's `Txn`); the integration tests (`TestLeasingTxnOwnerGet`,
`TestLeasingTxnOwnerIf`, `TestLeasingTxnRandIfThenOrElse`, `TestLeasingTxnAtomicCache`). Snippets:
`leasing/txn.go` (`ReqTxnCAS`, `ReqTxnReadOnly`), `leasing/unmet.go` (`UnmetTxnMissingKey`).

Proof sketch: `txn.eval()` (`txnLeasing.eval.spec`): an error (returned: no `Q`), or a cached answer
(`CachedAns (.txn st.req) σ0 res` with `etcdLb γ σ0`): the caller's update is opened at the current
state `σ` (`etcdLb_reach`: `Reach σ0 σ`, so the answer's revision is still reached: `CachedAns` at
`σ`) and committed with `σ' = σ`, `some res` (`LStep`'s cached case), its `Q` returned with the
reply; or nothing: `txn.serverTxn()` (`txnLeasing.serverTxn.spec`) with the caller's update.

Changes: the old specs (`specs-ref`'s `leasingKV__*.lean`) took the old client's
contracts at prefix `[]` (`isEtcdKV`, `isEtcdTxnKVO`), a revision certificate `etcdReached lo`, a
size bound (`OpShape`), and returned implementation outcomes (`getCached`, `getAcquired`,
`getNotAcquired`, `putCommitted`, `opCommitted`: the cache's states, its log, the history premise
`LeasingProtocol`); restated over W0's `etcdState` as a weakening of the KV contract (`Api.lean`'s
header): the caller's update persistent and over `lstep` (`LStep` with the marks of the keys
written through the KV: a cached answer is W0's serializable one for an unmarked key, the old proof's
"Theorem 1"), an error settling nothing; no size bound
(W0: the gRPC boundary fails on an oversized message), no certificate (the answer's revision is in
the update's state), no history premise (the contract claims nothing a protocol violation could
break). The old `commitOutcome` (`evalResult`: the cache's log state;
`txnCommitResult`) is now one update over `LStep`.

Margin: a cached answer is only shaped like one (the cache's comparison is not etcd's:
`issues/leasing-evalcmp-missing-key.md`; then the other branch's writes are not sent); an answer from
a member is the transaction's, applied any number of times (a guard's failure only retries).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `txn.Commit` of a leasing transaction (`LTxn.CommitTriple`). -/
def txnLeasing.Commit.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface),
  LTxn.CommitTriple (GF := GF) (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"Commit")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx

end spec

end Leasing
end EtcdGrove
end Perennial
