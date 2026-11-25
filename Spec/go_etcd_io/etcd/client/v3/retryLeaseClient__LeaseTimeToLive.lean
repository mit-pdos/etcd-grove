/-
`(*clientv3.retryLeaseClient).LeaseTimeToLive(ctx, in, opts...)` (`client/v3/retry.go`; the closed lease
example, notes/lease-ex-plan.md). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rlc.LeaseTimeToLive(ctx, in, opts...)` on a `*retryLeaseClient` over a stub on a connection to
`addr`: `rlc.lc.LeaseTimeToLive(ctx, in, append(opts, withRepeatablePolicy())...)` (the options' slice
full, `len = cap`: the `append` reallocates): the call's answer (`leaseTTLCallOut`). (Auth-lease S4, Freeze §2.3) Metadata-indexed: the spec `Spec` at every metadata an attempt may deliver
(`attemptPre`, as `kVClient.Put`'s; a plain spec is `GrpcSpec.md`); persistent, since the call may be
retried. -/
abbrev retryLeaseClient.LeaseTimeToLive.spec : Prop :=
  ∀ (rlc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse)
    (Q : LeaseTTLRespM → IProp GF) (ctx : GoInterfaceOk) (om : GrpcMd) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.LeaseTimeToLiveRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (retryLeaseAt rlc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.Lease/LeaseTimeToLive" Spec ∗
      metadata.outMD ctx om ∗ □ ▷ attemptPre conn om Spec (req.ID', req.Keys') Q ∗ ctxOk ctx cd ∗ inp ↦ req ∗
      opts ↦*□ vs ∗ ⌜opts.len = opts.cap⌝ ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝) }}
    (App (App (App (Val (rlc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!!
        go!"LeaseTimeToLive")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗ ((∃ req' : etcdserverpb.LeaseTimeToLiveRequest, inp ↦ req') ∗ leaseTTLCallOut Q resp err) }}

end spec

end EtcdGrove
end Perennial
