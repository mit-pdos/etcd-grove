/-
Lean-first (no Rocq counterpart).

The in-process client's laws (`inProcEtcd_laws.law`, `EtcdClientInProc.lean`) from the linked specs of
the calls: the kubernetes client's (`kubernetes/Link.lean`), the clientv3 `Get`'s (`ClientPutGet`), its
`Endpoints` and transaction builder's (`client/v3/Link.lean`, `LinkMembers.lean`). A linking module
(`*Linked`): the drivers' `Link`s pass it as `=k8s.inProcEtcd_laws_law_holds`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClientInProc
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.LinkMembers
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.kubernetes

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem inProcEtcd_laws_law_holds : inProcEtcd_laws.law (GF := GF) (hG := hG) := by
  intro _ ms V
  exact inProcEtcd_laws (fun {_} => kubernetes.Client.wp_Get) (fun {_} => kubernetes.Client.wp_List)
    (fun {_} => kubernetes.Client.wp_OptimisticPut) (fun {_} => kubernetes.Client.wp_OptimisticDelete)
    client.client_range_any_law_holds client.v3.Client.wp_Endpoints client.v3.kv.wp_Txn
    client.v3.txn.wp_If client.v3.txn.wp_Then client.v3.txn.wp_Else client.v3.txn.wp_CommitM ms V

end linked

end k8s
end EtcdGrove
end Perennial
