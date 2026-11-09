/-
`(*leasingKV).Delete` (`client/v3/leasing/kv.go`).

Users: the integration tests (`lkv.Delete(ctx, "k")`, `WithPrefix`, `WithFromKey`, `WithRange`,
`WithPrevKV`: `TestLeasingDeleteOwner`, `TestLeasingOwnerDeletePrefix`, `TestLeasingDeleteRangeBounds`);
the proxy goes through `Do`. Snippets: `leasing/writes.go` (`ReqDeleteRange`), `leasing/unmet.go`
(`UnmetDeleteRangePrevKV`).

Proof sketch: `OpDelete.spec` (W0; `¬ prefixAndFromKey gs`, `¬ deletePanics`) builds `opAt op
(opDeleteM key gs)`; then `leasingKV.delete.spec` at that `op`, the call's principal `p` and `lo = 0` (`authLb γ 0`:
its first disjunct).

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
break). **New**: a range delete is the request without `prevKv` (`execReq`:
`deleteRangeRPC` drops the option, a finding of this batch).

Margin: as `Put`'s: applied any number of times; a range delete reports no previous key-values even
if asked.
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

/-- `lkv.Delete` meets the leasing contract's `Delete` (`LKV.DeleteTriple`). -/
def leasingKV.Delete.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  LKV.DeleteTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Delete")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL)) γ who pfx γL

end spec

end Leasing
end EtcdGrove
end Perennial
