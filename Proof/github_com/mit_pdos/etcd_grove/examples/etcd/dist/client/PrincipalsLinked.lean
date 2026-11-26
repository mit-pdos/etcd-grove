/- Lean-first (no Rocq counterpart).

# The auth workload's principal calls, linked (#50 F7 S7, `notes/etcd-dist-f7.md`)

`principalCodec` over `enc`, and `remotePrincipals` (the orchestrator's side of the principal service: `Report` at
the principals' wire, `CallAll`'s goroutines) at `principalsShare`. `RunAuth` and NodeMain's auth arm are not linked
yet (`etcd_auth.Work`'s dist proof, `principalOp`'s, is open).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remotePrincipals
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CallAll
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section links
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [auth_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [rem_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]

/-- The principals' codec, linked over `enc`. -/
theorem wp_principalCodec : principalCodec.spec (GF := GF) (hG := hG) :=
  principalCodec.wp_proof EtcdGrove.enc.Enc.wp_Str EtcdGrove.enc.Enc.wp_Bool EtcdGrove.enc.wp_NewDec
    EtcdGrove.enc.Dec.wp_Str EtcdGrove.enc.Dec.wp_Bool EtcdGrove.enc.Dec.wp_Done

/-- **The principals' remote calls, linked** (`Report` at the principals' wire, `CallAll`'s goroutines), at
`principalsShare`. -/
theorem wp_remotePrincipals : remotePrincipals.spec (GF := GF) (hG := hG) :=
  remotePrincipals.wp_proof EtcdGrove.etcd_auth.wp_Principals
    (reportAll.wp_proof CallAll.wp_proof (fun {_ _ _ _ _ _} => EtcdGrove.remote.wp_Report))
    wp_principalCodec

end links

end etcd_dist_client
end EtcdGrove
end Perennial
