/-
`(*etcdserverpb.leaseClient).LeaseKeepAlive(ctx, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the
generated Lease stub; item 1, the client lease). Lean-first (no Rocq counterpart).
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

/-- `c.LeaseKeepAlive(ctx, opts...)` on a stub on a connection to the server at `addr`
(`leaseStubAt`, an etcd connection) serving the keep-alive stream: `NewStream` of
`"/etcdserverpb.Lease/LeaseKeepAlive"` with `grpc.StaticMethod()` before the options and the Lease
service's stream descriptor (`leaseDescOk`), wrapped in a `GenericClientStream`: the client end of
a fresh stream (both tokens at `[]`), or a `nil` stream and a client error. -/
abbrev leaseClient.LeaseKeepAlive.spec : Prop :=
  ∀ (lc conn : Loc) (addr : GoString) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ leaseStubAt lc conn ∗
      isEtcdConn conn [addr] ∗ leaseKAStreamOk addr ∗ leaseDescOk ∗ ctxOk ctx cd ∗
      opts ↦*□ vs ∗ streamCallOptsOk vs }}
    (App (App (Val (lc @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseKeepAlive"))
      (Val #(GoInterface.ok ctx))) (Val #opts))
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
