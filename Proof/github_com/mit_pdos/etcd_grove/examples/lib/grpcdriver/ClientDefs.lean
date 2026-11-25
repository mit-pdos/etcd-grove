/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the client's environment

`drvCli γid γb c ids` (persistent): what every section of the client (`echo`, `fail`, `meta`,
`canceled`, `serverStream`, `clientStream`, `bidi`) runs with: the driver's package initialized, the
id counter `ids` (`isCtr`), and the generated stub `c` (a `*svc.driverClient`, as `svc.DriverClient`)
over a connection `conn` to the server's address, dialed with no interceptor (`grpcConn conn
[drvAddr] [] [] anyRes`), at which the service's methods are registered with their specs
(`isGrpcRpcMd`, `Svc.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Svc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- The generated stub `c` (`svc.NewDriverClient(conn)`): a `*driverClient` whose `cc` is the
`*grpc.ClientConn` `conn` (persistent). -/
def drvStubAt (c : GoInterface) (conn : Loc) : IProp GF :=
  iprop(∃ dc : Loc, ⌜c = interface.mkOk (go.GoType.PointerType svc.driverClient.ty) #dc⌝ ∗
    structFieldRef svc.driverClient go!"cc" dc ↦□
      (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #conn :
        GoInterface))

instance drvStubAt_persistent (c : GoInterface) (conn : Loc) :
    Persistent (drvStubAt (GF := GF) c conn) := by
  unfold drvStubAt; infer_instance

/-- The client's environment (see the file header). -/
def drvCli (γid γb : GName) (c : GoInterface) (ids : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
    drvFacts ∗ isCtr γid γb ids ∗
    ∃ conn : Loc, drvStubAt c conn ∗ grpcConn conn [drvAddr] [] [] anyRes ∗
      isGrpcRpcMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr echoName (echoSpec γid) ∗
      isGrpcRpcMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr failName failSpec ∗
      isGrpcRpcMd (Req := (pbStringValueT (GF := GF)).toProtoMsg)
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr metaName metaSpec)

instance drvCli_persistent (γid γb : GName) (c : GoInterface) (ids : Loc) :
    Persistent (drvCli (GF := GF) γid γb c ids) := by
  unfold drvCli; infer_instance

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
