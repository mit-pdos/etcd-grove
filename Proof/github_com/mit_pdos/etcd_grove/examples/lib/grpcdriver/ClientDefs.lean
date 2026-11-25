/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the client's environment

`drvCli γid γb c ids` (persistent): what every section of the client (`echo`, `fail`, `meta`,
`canceled`, `serverStream`, `clientStream`, `bidi`) runs with: the driver's package initialized, the
id counter `ids` (`isCtr`), and the generated stub `c` (a `*svc.driverClient`, as `svc.DriverClient`)
over a connection `conn` to the server's address, dialed with no interceptor (`grpcConn conn
[drvAddr] [] [] anyRes`), at which the service's methods are registered with their specs
(`isGrpcRpcMd`, `Svc.lean`), the streams' facts (`drvStrmFacts`), and no per-RPC credentials
(`connCredsOk conn []`: an attempt's metadata is the caller's).
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

/-- **What the client's streams need of its connection** (persistent): its options set no stream
interceptor (`grpcConnOpts`, `streamIc = none`), and the three streams registered at the server's
address with the table's specifications (`strmSpec`: a response's content is the entry's `dn`). -/
def drvStrmFacts (conn : Loc) : IProp GF :=
  iprop(□ ((∃ d : GrpcConnOpts, grpcConnOpts conn d ∗ ⌜d.streamIc = none⌝) ∗
    isGrpcStreamMd (Req := strmMsg (GF := GF))
      (Rep := strmMsg (GF := GF)) drvAddr serverStreamName ssUp (strmSpec ssDn) ∗
    isGrpcStreamMd (Req := strmMsg (GF := GF))
      (Rep := strmMsg (GF := GF)) drvAddr clientStreamName csUp (strmSpec csDn) ∗
    isGrpcStreamMd (Req := strmMsg (GF := GF))
      (Rep := strmMsg (GF := GF)) drvAddr bidiName biUp (strmSpec biDn)))

instance drvStrmFacts_persistent (conn : Loc) : Persistent (drvStrmFacts (GF := GF) conn) := by
  unfold drvStrmFacts; infer_instance

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
        (Rep := (pbStringValueRT (GF := GF)).toProtoMsg) drvAddr metaName metaSpec ∗
      drvStrmFacts conn ∗ connCredsOk conn [] (fun _ => iprop(True)))

instance drvCli_persistent (γid γb : GName) (c : GoInterface) (ids : Loc) :
    Persistent (drvCli (GF := GF) γid γb c ids) := by
  unfold drvCli; infer_instance

/-- **`context.Background()` is quiet**: its `Done()` and `Err()` (the embedded `emptyCtx`'s) return
`nil`, and it has no deadline (as client/v3's `ctxQuiet_background`, without that package's
assumptions). -/
theorem drv_ctxQuiet_background : ⊢ ctxQuiet (GF := GF) context.backgroundCtxVal := by
  unfold ctxQuiet
  isplitl
  · iintro !> %Φ HΦ
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    iexact HΦ
  isplitl
  · iintro !> %Φ HΦ
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    iexact HΦ
  unfold ctxDeadline
  iintro !> %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ

end defs

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

end Perennial
