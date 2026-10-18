/-
`(*clientv3.retryLeaseClient).LeaseKeepAlive(ctx, opts...)` (`client/v3/retry.go`; item 1, the client
lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `rlc.LeaseKeepAlive(ctx, opts...)` on a `*retryLeaseClient` over a stub on a connection to
`addr` serving the keep-alive stream: `rlc.lc.LeaseKeepAlive(ctx, append(opts,
withRepeatablePolicy())...)` (the options' slice full): a client end of a new stream, both tokens at
`[]`, or a client error and a `nil` stream. -/
abbrev retryLeaseClient.LeaseKeepAlive.spec : Prop :=
  ∀ (rlc conn : Loc) (addr : GoString) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseAt rlc conn ∗
      isEtcdConn conn addr ∗ leaseKAStreamOk addr ∗ ctxOk ctx cd ∗
      opts ↦*□ vs ∗ ⌜opts.len = opts.cap⌝ ∗ streamCallOptsOk vs }}
    (App (App (Val (rlc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty @!!
        go!"LeaseKeepAlive")) (Val #(GoInterface.ok ctx))) (Val #opts))
  {{ (st err : GoInterface), RET (PairV #st #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : StreamNames) (Dn : Nat → (w64 × w64) → IProp GF)
          (cd' : context.ContextDesc (IProp GF)),
        cliBidiStreamIs st γ pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse
          (fun _ _ => iprop(True)) Dn cd' ∗
        cliSendTok (Req := pbLeaseKeepAliveRequest) γ [] ∗
        cliRecvTok (Rep := pbLeaseKeepAliveResponse) γ []) ∨
      (⌜st = GoInterface.nil⌝ ∗ cliStreamErr err) }}

end spec

end EtcdGrove
end Perennial
