/-
`etcdserverpb.RegisterAuthServer(s, srv)` (`api/etcdserverpb/rpc_grpc.pb.go`, generated; item 4, the
server start). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/google_golang_org/grpc/InvGrpcServer.lean`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `RegisterAuthServer(gs, srv)` on a server being built registers the service of
`Auth_ServiceDesc` (`grpcDescIs`, read-only; a service not registered yet, whose names are
distinct) with the service value `srv` (implementing the descriptor's handler type, with no
`testEmbeddedByValue`): `grpc.Server.RegisterService`'s registration. -/
abbrev etcdserverpb.RegisterAuthServer.spec : Prop :=
  ∀ (gs : Loc) (srv : GoInterface) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × val × GoInterface)) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
  {{ grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗
      grpcDescIs (globalAddr etcdserverpb.Auth_ServiceDesc) sn ht mds sds ∗ ⌜sn ∉ svcs⌝ ∗
      ⌜grpcImplements srv ht⌝ ∗ ⌜(descNames mds sds).Nodup⌝ ∗ ⌜grpcNoTestEmbedded srv⌝ }}
    (App (App (Val (@! etcdserverpb.RegisterAuthServer))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.Server.ty) #gs :
        GoInterface)))
      (Val #srv))
  {{ RET #(); grpcSrvNew gs ics sics (svcs ++ [sn]) (regs ++ descRegs sn mds srv)
      (sregs ++ descSRegs sn sds srv) }}

end spec

end EtcdGrove
end Perennial
