/-
`(*clientv3.kv).Put` (`client/v3/kv.go`).

Users: `client/v3/concurrency` (`Session`'s keys are written in transactions; `election.go` `Proclaim`
via `Txn`), `experimental/recipes` (`double_barrier.go:53` `Put` of the barrier key, `queue.go`,
`key.go:91` `putNewKV` via `Txn`), the examples (`examples/etcd/txnlin/linkvtxn.go:874` `callPut`,
`putget`, `putget3`, `compacted`, `compactwatch/compactkv.go`), Kubernetes' compactor
(`k8s.io/apiserver/pkg/storage/etcd3/compact.go`, through `Txn`). Snippets:
`clientv3kv/put_get.go` (`ReqPutThenGet`, `ReqPutRevision`), `clientv3kv/errors.go` (`ReqPutErrors`).

Proof sketch: `OpPut.spec` builds `opAt op (opPutM key val gs)` and gives back `optsAt opts gs` (its
premise `¬ putPanics`); then `kv.Do.spec` at that `op`, whose request is `.put (opPutM ...).putReq`
(`toReq` of a put), not a read, so it takes the caller's exclusive update unchanged; its post
`doReply` is `putReply res r.put' err` (or the indefinite case); `ContextError.spec` on that error
(`.etcd e` of `errVal e` by `callErr_errVal`: unchanged; an indefinite one: indefinite) gives the
post.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kv__Put.lean`: **relaxed**: any lease (was
`leaseID = 0`), auth on or off (the principal `who` of the handle), compaction and every mode, all
in the model's `Step`; no `opSizeOk` payload bound (the gRPC boundary must fail, not panic, on an
oversized message: `req/google_golang_org_grpc.md`); no `dup` flag (a write's update is exclusive:
the client sends a write once, the cluster applies an entry once: `req/` of 2c, 2d); **restated**:
the update over the client-owned `etcdState` (was the server's `etcdKV`), the answer `res` and the
reply's message model in place of `PutRespM`'s fields, the error classes (a definite error is a
linearized answer, `Q` given; an indefinite one gives nothing; was `kvErr`), the old `kvRevLb`
certificate subsumed by `etcdLb` (taken by the caller inside its update); no `kvRoom` (the
revision bound is the law `etcdState_revFits`).

Margin: on success the code also guarantees the reply's header names the member that
answered (`MemberId`, `RaftTerm`), not modelled; on an indefinite error the code may still have
applied the put (the update fires later or not at all), which is all the spec says.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Put` meets the KV contract's `Put` (`KV.PutTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Put.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.PutTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Put")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
