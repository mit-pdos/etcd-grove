/-
etcd's spec of `Auth.Authenticate` with auth on (`etcdAuthenticateSpec`): moved out of
`AuthnServedOn.lean` (2026-11-18), whose served theorems are over linked results, so that the specs
naming it import no linked result (CLAUDE.md, "Import tiers").
-/
module

public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.client.v3.ClientUser

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

end proofs

section proofsHF
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **etcd's spec of `Auth.Authenticate` with auth on, at the member's names `γa`**: a reply's
token is issued to the user named in the request (`auth.tokIssued`). The password and the
request's size ask nothing of the client: a wrong password, or a request too large, is an error. -/
def etcdAuthenticateSpecW (γa : auth.AuthNames) :
    GoString × GoString → (GoString → IProp GF) → IProp GF :=
  fun (m : GoString × GoString) (Φ : GoString → IProp GF) =>
    iprop(∀ t, auth.tokIssued γa t m.1 -∗ Φ t)

end proofsHF

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]


/-- **`etcdAuthenticateSpecW` at the messages' models** (S2, heap-free vocabulary, 2026-11-23: the
spec is `etcdAuthenticateSpecW`, over the models alone, what a service table holds; this is its form
at the message types). -/
def etcdAuthenticateSpec (γa : auth.AuthNames) :
    GrpcSpec (GF := GF) pbAuthenticateRequest pbAuthenticateResponse :=
  etcdAuthenticateSpecW γa

end proofs

end client
end EtcdGrove
end Perennial
