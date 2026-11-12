/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/RegisterAuthServer.lean` (item 4, the server
start). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.RegisterAuthServer
public import Spec.google_golang_org.grpc.Server__RegisterService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem etcdserverpb.RegisterAuthServer.wp_proof
    (wp_RegisterService : grpc.Server.RegisterService.spec (GF := GF) (hG := hG)) :
    etcdserverpb.RegisterAuthServer.spec (GF := GF) (hG := hG) := by
  intro gs srv ics sics svcs regs sregs sn ht mds sds
  wp_start as ⟨Hs, #Hd, %Hsn, %Himpl, %Hnd, %Hnt⟩
  obtain ⟨si, rfl, Hte⟩ := Hnt
  unfold testEmbeddedIface at Hte
  wp_auto
  simp only [Hte]
  wp_auto
  wp_apply (wp_RegisterService gs _ (GoInterface.ok si) ics sics svcs regs sregs sn ht mds sds)
    $$ [Hs] as Hs
  · iframe; iframe #; ipureintro; exact ⟨Hsn, Himpl, Hnd⟩
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
