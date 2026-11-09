/-
`(*txnLeasing).commitToCache` (`txn.go`): applies the committed user transaction's writes to the
cache. Proof sketch: `gatherResponseOps` (`gatherRespOk`: the one response is a transaction's, the
branches flat), write lock, `leaseCache.delete`/`Update` with the header (read-only: `Update` keeps
it; reached). The reply's fields are read at a share and given back (`serverTxn` then writes the
nested reply's header). Changes: from `specs-ref`'s `txnLeasing__commitToCache.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `commitToCache(txnResp, userTxn)`: the reply's `Header` and `Responses` fields and responses read
at a share `dq`, the header itself read-only for good (the cache may keep it). -/
def txnLeasing.commitToCache.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (ctx : GoInterface) (st : TxnSt) (resp hdr : Loc) (hm : HeaderM) (rsl : GoSlice) (dq : DFrac) (ms : List ResponseOpM)
    (σ0 : State) (userTxn : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗
      resp.[go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse, go!"Header"] ↦{dq} hdr ∗
      respHeaderOwn hdr DFrac.discard hm ∗
      resp.[go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse, go!"Responses"] ↦{dq} rsl ∗
      msgsOwn responseOpOwn rsl dq ms ∗ etcdLb γ σ0 ∗
      ⌜0 ≤ sint.Z hm.revision ∧ sint.Z hm.revision ≤ σ0.kv.rev⌝ ∗ opAt userTxn o ∗
      ⌜o.t = tTxn ∧ gatherRespOk ms [o]⌝ }}
    (App (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"commitToCache")) (Val #resp)) (Val #userTxn))
  {{ RET #(); ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗
      resp.[go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse, go!"Header"] ↦{dq} hdr ∗
      resp.[go_etcd_io.etcd.api.v3.etcdserverpb.TxnResponse, go!"Responses"] ↦{dq} rsl ∗
      msgsOwn responseOpOwn rsl dq ms }}

end spec

end Leasing
end EtcdGrove
end Perennial
