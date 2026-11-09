/-
# The Election service (`etcdserver/api/v3election`): vocabulary (batch 2e)

etcd serves the `v3electionpb.Election` gRPC service with an in-process client (`v3client`) and the
client's `concurrency` package (batch 1d): each call makes a session over the request's lease
(orphaned at once: its keep-alive ends with the request's context) and runs the `Election` method
of the same name. Its specs are therefore 1d's `Election.*` facts, read off the request's fields.

* `isElectionServer es c` (persistent): `es` is an `*electionServer` over the client `c`.
* `LeaderKeyM` (transparent): a `LeaderKey` (name, key, create revision, lease).
* The request and response messages (opaque, **provisional: 3h's message ownership** for
  `v3electionpb`): `campaignReq`, `proclaimReq`, `resignReq`, `leaderReq` (read-only, as gRPC
  hands them to a handler), `campaignResp`, `proclaimResp`, `resignResp`, `leaderResp` (fresh).

The service's registration on the member's gRPC server (2a) supplies the client and the caller's
principal (`ClientV3.ctxPrin`), and the caller's write permission (1d's `etcdPerm`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3election

open Iris Iris.BI

/-- A `LeaderKey`. -/
structure LeaderKeyM where
  name : GoString
  key : GoString
  rev : w64
  lease : w64

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- `es` is an `*electionServer` over the client `c` (persistent). -/
opaque isElectionServer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (es : Loc) (c : Loc) : IProp GF := iprop(True)

/-- A read-only `*CampaignRequest` (persistent). -/
opaque campaignReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (name : GoString) (lease : w64) (value : GoString) : IProp GF :=
  iprop(True)
/-- A read-only `*ProclaimRequest` (persistent). -/
opaque proclaimReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (lk : Option LeaderKeyM) (value : GoString) : IProp GF := iprop(True)
/-- A read-only `*ResignRequest` (persistent). -/
opaque resignReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (lk : Option LeaderKeyM) : IProp GF := iprop(True)
/-- A read-only `*LeaderRequest` (persistent). -/
opaque leaderReq [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (name : GoString) : IProp GF := iprop(True)

/-- A fresh `*CampaignResponse`: its header and leader key. -/
opaque campaignResp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (lk : LeaderKeyM) : IProp GF := iprop(True)
/-- A fresh `*ProclaimResponse`. -/
opaque proclaimResp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)
/-- A fresh `*ResignResponse`. -/
opaque resignResp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) : IProp GF := iprop(True)
/-- A fresh `*LeaderResponse` holding the key-value `v`. -/
opaque leaderResp [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (v : EtcdModel.KV) : IProp GF := iprop(True)

def isElectionServer_persistent.spec : Prop := ∀ es c, Persistent (isElectionServer (GF := GF) es c)

end res

end V3election
end EtcdGrove
end Perennial
