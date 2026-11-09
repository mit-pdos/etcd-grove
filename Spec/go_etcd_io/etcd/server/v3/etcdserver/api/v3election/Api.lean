/-
# The Election service (`etcdserver/api/v3election`): vocabulary (batch 2e)

etcd serves the `v3electionpb.Election` gRPC service with an in-process client (`v3client`) and the
client's `concurrency` package (batch 1d): each call makes a session over the request's lease
(orphaned at once: its keep-alive ends with the request's context) and runs the `Election` method
of the same name. Its specs are therefore 1d's `Election.*` facts, read off the request's fields.

* `isElectionServer es c` (persistent): `es` is an `*electionServer` over the client `c`.
* `LeaderKeyM` (transparent): a `LeaderKey` (name, key, create revision, lease): 3h's
  `V3electionpb.LeaderKeyM`.
* The request and response messages: 3h's (`V3electionpb`): `campaignReq`, `proclaimReq`,
  `resignReq`, `leaderReq` (read-only, as gRPC hands them to a handler), `campaignResp`,
  `proclaimResp`, `resignResp`, `leaderResp` (fresh). Verify-round (A8 completeness F4): the
  provisional opaque names are now abbreviations of 3h's, so the handler's decoded request and 3h's
  field and reply laws apply.

**The prefix.** `concurrency.NewElection(s, name)` campaigns under `name + "/"` (1d's
`NewElection.spec`): the facts these specs state are about `name ++ "/"` (verify-round, A3
completeness F1, A8 provability F6). `ResumeElection(s, name, key, rev)` keeps `name` as given (1d's
`ResumeElection.spec`); `Proclaim` and `Resign` use only the key and revision, so the prefix does
not matter there.

The service's registration on the member's gRPC server (2a) supplies the client and the caller's
principal (`ClientV3.ctxPrin`), and the caller's write permission (1d's `etcdPerm`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.v3electionpb.Api
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3election

open Iris Iris.BI

/-- A `LeaderKey`: 3h's. -/
abbrev LeaderKeyM : Type := V3electionpb.LeaderKeyM

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `es` is an `*electionServer` over the client `c` (persistent). -/
opaque isElectionServer [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (es : Loc) (c : Loc) : IProp GF := iprop(True)

/-- A read-only `*CampaignRequest` (persistent): 3h's. -/
abbrev campaignReq (p : Loc) (name : GoString) (lease : w64) (value : GoString) : IProp GF :=
  V3electionpb.campaignReq p name lease value
/-- A read-only `*ProclaimRequest` (persistent): 3h's. -/
abbrev proclaimReq (p : Loc) (lk : Option LeaderKeyM) (value : GoString) : IProp GF :=
  V3electionpb.proclaimReq p lk value
/-- A read-only `*ResignRequest` (persistent): 3h's. -/
abbrev resignReq (p : Loc) (lk : Option LeaderKeyM) : IProp GF := V3electionpb.resignReq p lk
/-- A read-only `*LeaderRequest` (persistent): 3h's. -/
abbrev leaderReq (p : Loc) (name : GoString) : IProp GF := V3electionpb.leaderReq p name

/-- A fresh `*CampaignResponse`: its header and leader key (3h's). -/
abbrev campaignResp (p : Loc) (lk : LeaderKeyM) : IProp GF := V3electionpb.campaignResp p lk
/-- A fresh `*ProclaimResponse` (3h's). -/
abbrev proclaimResp (p : Loc) : IProp GF := V3electionpb.proclaimResp p
/-- A fresh `*ResignResponse` (3h's). -/
abbrev resignResp (p : Loc) : IProp GF := V3electionpb.resignResp p
/-- A fresh `*LeaderResponse` holding the key-value `v` (3h's). -/
abbrev leaderResp (p : Loc) (v : EtcdModel.KV) : IProp GF := V3electionpb.leaderResp p v

def isElectionServer_persistent.spec : Prop := ∀ es c, Persistent (isElectionServer (GF := GF) es c)

end res

end V3election
end EtcdGrove
end Perennial
