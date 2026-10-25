/-
`(*routingClientConn).Invoke(ctx, method, args, reply, opts...)` (`client/v3/channel_pool.go:94`,
PR #21765): looks up the connection for `ctx` via `r.client.connectionForContext(ctx)` and, if
found, invokes `conn.Invoke(ctx, method, args, reply, opts...)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__connectionForContext
public import Proof.go_etcd_io.etcd.client.v3.EtcdInvoke

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

abbrev routingClientConn.Invoke.spec : Prop :=
  ∀ (rcc cl mu mref : Loc) (dq0 dq1 : DFrac)
    (chs : GMap GoString go_etcd_io.etcd.client.v3.channel)
    (o : Option GoString) (addr : List GoString) (method : GoString) (Req Rep : ProtoMsg GF)
    (Spec : GrpcSpec Req Rep) (m : Req.M) (Φ : Rep.M → IProp GF) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (inp out : Loc) (opts : GoSlice)
    (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.routingClientConn go!"client" rcc ↦{dq0} cl ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      clientv3.ctxChannelKeyIs (GoInterface.ok ctx) o ∗
      if poolConnFor chs o = null then
        iprop(True)
      else
        iprop(isEtcdConn (poolConnFor chs o) addr ∗ isGrpcRpcs addr method Spec ∗
          reqPre (poolConnFor chs o) method addr vs (Spec m Φ) ∗ ctxOk ctx cd ∗
          Req.send inp m ∗ Rep.blank out ∗ opts ↦*□ vs ∗ callOptsOk vs) }}
    (App (App (App (App (App
      (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.v3.routingClientConn.ty)
        go!"Invoke" #rcc))
      (Val #(GoInterface.ok ctx))) (Val #method))
      (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #inp : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType Rep.ty) #out : GoInterface)))
      (Val #opts))
  {{ (err : GoInterface), RET #err;
      structFieldRef go_etcd_io.etcd.client.v3.routingClientConn go!"client" rcc ↦{dq0} cl ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq1} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      if poolConnFor chs o = null then
        ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗
          go_etcd_io.etcd.cache.v3.errorStringSpec e
      else
        Req.send inp m ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ m' : Rep.M, Rep.recv out m' ∗ Φ m') ∨
          (⌜err ≠ GoInterface.nil ∧ clientErr err⌝ ∗ statusErrOk err ∗ errCellOk err)) }}

end spec

end EtcdGrove
end Perennial
