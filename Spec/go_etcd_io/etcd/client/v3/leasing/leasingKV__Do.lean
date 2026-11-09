/-
`(*leasingKV).Do` (`client/v3/leasing/kv.go`).

Users: the gRPC proxy, for every KV request (`server/proxy/grpcproxy/kv.go:62` `Range`
(`RangeRequestToOp`), `:86` `Put`, `:94` `DeleteRange`, `:116` `Txn` (`TxnRequestToOp`: `OpTxn` over
slices of exactly their length, nested transactions as nested `OpTxn`s)); the integration tests
(`TestLeasingDo`). Snippets: `leasing/txn.go` (`ReqDoProxyRange`, `ReqDoTxn`).

Proof sketch: the getters (`Op.IsGet`, ... W0's specs over `opAt`) select the case; a range:
`leasingKV.get.spec` (the open token's share used), then `GetResponse.OpResponse.spec`; a put:
`leasingKV.put.spec`; a delete: `leasingKV.delete.spec`; a transaction: `Op.Txn.spec` (W0: the
comparisons and branches, read-only), then `leasingKV.Txn.spec`, `LTxn.IfTriple`, `ThenTriple`,
`ElseTriple` (`opsCapOk` of the branches, from `opCapOk op`), `CommitTriple` with the caller's update (its request is
`.txn st.req` with `st` the comparisons and branches' requests: `toReq`'s); then
`TxnResponse.OpResponse.spec`. The update is `lstep γL pfx p lo rq` throughout (the internal `put`/`delete` at this `lo`), the marks
`reqWrites rq` (`toReq`). An `Op` of no
type is excluded by `toReq` (the code returns an empty response, no panic).

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
break). **Nested transactions** (was flat only): a nested transaction's branch slices without spare
capacity (`opCapOk`: `gatherOps` appends into them, `nonissues/leasing-gatherops-spare-capacity.md`);
the proxy's `TxnRequestToOp` `make`s them so. **New**: the marks of the request's writes.

Margin: as the three operations' and `Commit`'s.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Api

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

/-- `lkv.Do` meets the leasing contract's `Do` (`LKV.DoTriple`). -/
def leasingKV.Do.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (q : Qp),
  LKV.DoTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Do")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ lkvOpen γL q)) γ who pfx γL

end spec

end Leasing
end EtcdGrove
end Perennial
