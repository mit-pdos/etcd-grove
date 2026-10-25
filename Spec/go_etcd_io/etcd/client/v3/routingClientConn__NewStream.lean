/-
`(*routingClientConn).NewStream(ctx, desc, method, opts...)` (`client/v3/channel_pool.go:102`,
PR #21765): looks up the connection for `ctx` via `r.client.connectionForContext(ctx)` and, if
found, calls `conn.NewStream(ctx, desc, method, opts...)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__connectionForContext
public import Spec.google_golang_org.grpc.ClientConn__NewStream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

abbrev routingClientConn.NewStream.spec : Prop :=
  ∀ (rcc cl mu mref : Loc) (dq0 dq1 : DFrac)
    (chs : GMap GoString go_etcd_io.etcd.client.v3.channel)
    (o : Option GoString) (addrs : List GoString) (ics : List GoFunc) (method : GoString)
    (Req Rep : StreamMsg GF) (Up : GoString → Nat → Req.M → IProp GF)
    (Spec : GoString → StreamSpec Rep) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (desc : Loc) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.routingClientConn go!"client" rcc ↦{dq0} cl ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      clientv3.ctxChannelKeyIs (GoInterface.ok ctx) o ∗
      if poolConnFor chs o = null then
        iprop(True)
      else
        iprop(grpcConn (poolConnFor chs o) addrs ics [] ∗ isGrpcStreams addrs method Up Spec ∗
          ctxOk ctx cd ∗
          (∃ d : google_golang_org.grpc.StreamDesc, desc ↦□ d ∗ ⌜d.ClientStreams' = true⌝) ∗
          opts ↦*□ vs ∗ streamCallOptsOk vs) }}
    (App (App (App (App
      (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.v3.routingClientConn.ty)
        go!"NewStream" #rcc))
      (Val #(GoInterface.ok ctx))) (Val #desc)) (Val #method)) (Val #opts))
  {{ (cs err : GoInterface), RET (PairV #cs #err);
      structFieldRef go_etcd_io.etcd.client.v3.routingClientConn go!"client" rcc ↦{dq0} cl ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      if poolConnFor chs o = null then
        ⌜cs = GoInterface.nil⌝ ∗
          ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗
            go_etcd_io.etcd.cache.v3.errorStringSpec e
      else
        (⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (γ : StreamNames)
            (Dn : Nat → Rep.M → IProp GF) (cd' : context.ContextDesc (IProp GF)),
          ⌜a ∈ addrs⌝ ∗ cliStreamIs cs γ Req Rep (Up a) Dn cd' ∗ cliSendTok (Req := Req) γ [] ∗
          cliRecvTok (Rep := Rep) γ [] ∗ Spec a γ Dn) ∨
        (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
