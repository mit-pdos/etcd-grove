/-
`(*Client).connectionForContext(ctx)` (`client/v3/channel_pool.go:68`, PR #21765): resolves the
request's channel key via `channelKeyForRequest(ctx)`, acquires `c.epMu.RLock()`, looks up
`c.channels[key]`, releases `c.epMu.RUnlock()`, and returns:
- `(nil, c.connectionPoolClosedError())` if `c.channels == nil` (`Client.connectionForContext_closed.spec`),
- `(nil, fmt.Errorf("%w: %q", ErrChannelKeyNotFound, key))` if `ch.conn == nil`,
- `(ch.conn, nil)` otherwise (`Client.connectionForContext.spec`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.channelKeyForRequest
public import Spec.go_etcd_io.etcd.client.v3.Client__connectionPoolClosedError

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

/-- What `c.epMu` guards when the channel pool is active: `c.channels` pointing to map `mref` with
entries `chs`. -/
abbrev clientPoolInv (cl mref : Loc)
    (chs : GMap GoString go_etcd_io.etcd.client.v3.channel) (q : Qp) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.client.v3.Client go!"channels" cl ↦{DFrac.own q} mref ∗
    mref ↦${DFrac.own q} chs)

/-- What `c.epMu` guards after `c.Close()` sets `c.channels = nil`. -/
abbrev clientPoolClosedInv (cl : Loc) (q : Qp) : IProp GF :=
  iprop(structFieldRef go_etcd_io.etcd.client.v3.Client go!"channels" cl ↦{DFrac.own q} map.nil)

/-- The `*grpc.ClientConn` stored in `chs` for the context's channel key `o` (`null` if absent). -/
abbrev poolConnFor (chs : GMap GoString go_etcd_io.etcd.client.v3.channel)
    (o : Option GoString) : Loc :=
  ((chs !! clientv3.reqChannelKey o).getD (zero_val go_etcd_io.etcd.client.v3.channel)).conn'

/-- `c.connectionForContext(ctx)` on an active channel pool `chs`. -/
abbrev Client.connectionForContext.spec : Prop :=
  ∀ (cl mu mref : Loc) (dq : DFrac)
    (chs : GMap GoString go_etcd_io.etcd.client.v3.channel)
    (ctx : GoInterface) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      clientv3.ctxChannelKeyIs ctx o }}
    (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty)
      go!"connectionForContext" #cl)) (Val #ctx))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq} mu ∗
      sync.ownRWMutex mu (clientPoolInv cl mref chs) ∗
      if poolConnFor chs o = null then
        ⌜conn = null⌝ ∗
          ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗
            go_etcd_io.etcd.cache.v3.errorStringSpec e
      else
        ⌜conn = poolConnFor chs o ∧ err = GoInterface.nil⌝ }}

/-- `c.connectionForContext(ctx)` on a closed channel pool (`c.channels == nil`). -/
abbrev Client.connectionForContext_closed.spec : Prop :=
  ∀ (cl mu : Loc) (dq0 dq1 : DFrac) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (st : Broadcast) (ctx : GoInterface) (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq0} mu ∗
      sync.ownRWMutex mu (clientPoolClosedInv cl) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦{dq1} GoInterface.ok ci ∗
      ctxErrClient ci cd ∗
      (match st with
       | .Done => context.ContextClosed cd.Done_gn
       | _ => iprop(True)) ∗
      clientv3.ctxChannelKeyIs ctx o }}
    (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty)
      go!"connectionForContext" #cl)) (Val #ctx))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err);
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"epMu" cl ↦{dq0} mu ∗
      sync.ownRWMutex mu (clientPoolClosedInv cl) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" cl ↦{dq1} GoInterface.ok ci ∗
      ⌜conn = null ∧ err ≠ GoInterface.nil ∧ (st = .Done → clientErr err)⌝ ∗
      statusErrOk err ∗
      (match st with
       | .Done => errCellOk err
       | _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
