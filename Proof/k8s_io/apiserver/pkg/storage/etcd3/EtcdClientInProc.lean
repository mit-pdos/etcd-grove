/-
Lean-first (no Rocq counterpart).

# The in-process instance of the k8s library's etcd client (K5, `notes/k8s-dist-lean-plan.md` §4.1)

`inProcEtcd ms V`: a client of the in-process members `ms` (`client.SrvAt`), whose handle is `New`'s
client of them (`isNewClient`, sending a write at most once, each member's KV registered), with an
update at every member's KV, live when no member refuses connections. `inProcEtcd_laws`: its laws,
from the in-process specs of the calls (hypotheses, which the linking modules pass).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.EtcdClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver EtcdGrove.kubernetes

section inproc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The client of the in-process members `ms`** (see the file header). -/
def inProcEtcd [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : K8sEtcd GF where
  kvs := ms.map (fun x => x.γr.kv)
  live := ∀ x ∈ ms, noRefusalAt x.addr
  eps := ms.map client.SrvAt.addr
  handle cl := iprop(isNewClient cl (ms.map client.SrvAt.addr) V ∗
    client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ [∗list] x ∈ ms, client.kvRegsAt x)

theorem inProcEtcd_kvs [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) :
    (inProcEtcd ms V).kvs = ms.map (fun x => x.γr.kv) := rfl

/-- **The in-process client's laws**, from the in-process specs. -/
theorem inProcEtcd_laws [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (wp_Get : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.Get.spec (GF := GF) (hG := hG))
    (wp_List : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.List.spec (GF := GF) (hG := hG))
    (wp_OptimisticPut : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticPut.spec (GF := GF) (hG := hG))
    (wp_OptimisticDelete : ∀ [go_etcd_io.etcd.client.v3.kubernetes.Assumptions],
      kubernetes.Client.OptimisticDelete.spec (GF := GF) (hG := hG))
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) : (inProcEtcd ms V).Laws where
  get := by
    intro _ _ _ kc ci cd key opts Q h1 h2
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_Get kc ms V ci cd key opts Q h1 h2) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  list := by
    intro _ _ _ kc ci cd pfx opts Q h1 h2 h3 h4 h5
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, -, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_List kc ms V ci cd pfx opts Q h1 h2 h3 h4 h5) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticPut := by
    intro _ _ _ kc ci cd key vsl val rev opts Q h1 h2 h3
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, #Hv, Hau⟩ HΦ
    iapply (wp_OptimisticPut kc ms V ci cd key vsl val rev opts Q h1 h2 h3) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ
  optimisticDelete := by
    intro _ _ _ kc ci cd key rev opts Q h1
    simp only [inProcEtcd, BigAndL.bigAndL_map]
    iintro %Φ ⟨#P1, #P2, Hlt, ⟨#Hnc, #Hwo, #Hregs⟩, #Hctx, #Hce, Hau⟩ HΦ
    iapply (wp_OptimisticDelete kc ms V ci cd key rev opts Q h1) $$ [Hlt Hau] [HΦ]
    · iframe Hlt Hau
      iframe #
    · iexact HΦ

/-- **The in-process client** from `New`'s client of the members (`isStore`'s former conjuncts). -/
theorem k8sClient_inProc [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (hl : (inProcEtcd ms V).Laws) (cl : Loc) :
    isNewClient cl (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗ ([∗list] x ∈ ms, client.kvRegsAt x) ⊢
    k8sClient (inProcEtcd ms V) cl := by
  iintro #H
  unfold k8sClient
  isplitr
  · ipureintro; exact hl
  imodintro
  simp only [inProcEtcd]
  iexact H

end inproc

end k8s
end EtcdGrove
end Perennial
