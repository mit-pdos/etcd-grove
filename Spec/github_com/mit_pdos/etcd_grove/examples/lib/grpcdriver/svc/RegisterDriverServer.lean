/- Lean-first (no Rocq counterpart).

`svc.RegisterDriverServer(gs, srv)` (`svc/svc.go`): on a server being built, registers the service
of `Driver_ServiceDesc` (`grpcDescIs`, read-only; a service not registered yet, whose names are
distinct and whose streams set a stream flag) with the service value `srv` (implementing the
descriptor's handler type): `grpc.Server.RegisterService`'s registration, as etcd's
`RegisterKVServer` (the driver's has no `testEmbeddedByValue` check).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc.StreamDefs
public import Proof.google_golang_org.grpc.InvGrpcServer

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- See the file header. -/
abbrev RegisterDriverServer.spec : Prop :=
  ∀ (gs : Loc) (srv : GoInterface) (ics sics : List GoFunc) (svcs : List GoString)
    (regs sregs : List (GoString × GoFunc × GoInterface)) (sn : GoString) (ht : GoInterface)
    (mds : List google_golang_org.grpc.MethodDesc) (sds : List google_golang_org.grpc.StreamDesc),
  {{ grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗
      grpcDescIs (globalAddr Driver_ServiceDesc) sn ht mds sds ∗ ⌜sn ∉ svcs⌝ ∗
      ⌜grpcImplements srv ht⌝ ∗ ⌜(descNames mds sds).Nodup⌝ ∗
      ⌜∀ sd ∈ sds, sd.ClientStreams' = true ∨ sd.ServerStreams' = true⌝ }}
    (App (App (Val (@! RegisterDriverServer))
      (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.Server.ty) #gs :
        GoInterface)))
      (Val #srv))
  {{ RET #(); grpcSrvNew gs ics sics (svcs ++ [sn]) (regs ++ descRegs sn mds srv)
      (sregs ++ descSRegs sn sds srv) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.svc
end Perennial
