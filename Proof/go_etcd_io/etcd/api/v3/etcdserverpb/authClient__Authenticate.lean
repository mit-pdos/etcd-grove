/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/authClient__Authenticate.lean` (the auth plan's
C1; phase 1, `sorry`: the stub's `Authenticate` is not translated yet). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.authClient__Authenticate
public import Spec.google_golang_org.grpc.StaticMethod
public import Spec.google_golang_org.grpc.ClientConn__Invoke

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem etcdserverpb.authClient.Authenticate.wp_proof
    (wp_StaticMethod : grpc.StaticMethod.spec (GF := GF) (hG := hG))
    (wp_Invoke : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)) :
    etcdserverpb.authClient.Authenticate.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
