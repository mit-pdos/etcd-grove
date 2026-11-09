/-
`(*leasingKV).Put` (`client/v3/leasing/kv.go`).

Users: the integration tests (`lkv.Put(ctx, "k", "v")`, `WithPrevKV`: `TestLeasingPrevKey`,
`TestLeasingOwnerPutResponse`); the proxy goes through `Do`. Snippets: `leasing/writes.go`
(`ReqPutRevision`, `ReqPutError`), `leasing/unmet.go` (`UnmetPutOnce`, `UnmetPutModRevision`).

Proof sketch: `OpPut.spec` (W0; `¬ putPanics`) builds `opAt op (opPutM key val gs)`; then
`leasingKV.put.spec` at that `op` with the caller's update.

Changes: the old specs (`specs-ref`'s `leasingKV__*.lean`) took the old client's
contracts at prefix `[]` (`isEtcdKV`, `isEtcdTxnKVO`), a revision certificate `etcdReached lo`, a
size bound (`OpShape`), and returned implementation outcomes (`getCached`, `getAcquired`,
`getNotAcquired`, `putCommitted`, `opCommitted`: the cache's states, its log, the history premise
`LeasingProtocol`); restated over W0's `etcdState` as a weakening of the KV contract (`Api.lean`'s
header): the caller's update persistent and over `LStep`, an error settling nothing; no size bound
(W0: the gRPC boundary fails on an oversized message), no certificate (the answer's revision is in
the update's state), no history premise (the contract claims nothing a protocol violation could
break). The old `putCommitted` (the cache's step) is internal now.

Margin: on success the put was applied at least once, and the reply is one application's answer;
it may have been applied more often (`issues/leasing-modify-uncached-once.md`: twice whenever the
key was not cached and no other client held it), each application firing the caller's update; the
reply is read-only.
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

/-- `lkv.Put` meets the leasing contract's `Put` (`LKV.PutTriple`). -/
def leasingKV.Put.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  LKV.PutTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Put")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL)) γ who pfx

end spec

end Leasing
end EtcdGrove
end Perennial
