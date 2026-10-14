/-
`(*etcdserverpb.kVClient).Range(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
KV stub; translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- `c.Range(ctx, in, opts...)` on a stub on a connection to `K` (`kvStubAt`): `Invoke` of
`"/etcdserverpb.KV/Range"` with `grpc.StaticMethod()` before the options, into a new
`*RangeResponse`: the call's answer (`rangeCallOut`, the run's `Q`); the request comes back. -/
abbrev kVClient.Range.spec : Prop :=
  ∀ (kc conn : Loc) (K : KVConn GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.RangeRequest) (k e : GoString) (opts : GoSlice)
    (vs : List GoInterface) (Q : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isKVConn conn K ∗ context.isContext ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.RangeEnd' ↦*□ e ∗
      opts ↦*□ vs ∗ callOptsOk vs ∗ rangeRunOk K (rangeReqOp req k e) Q }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.RangeRequest, inp ↦ req') ∗ rangeCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
