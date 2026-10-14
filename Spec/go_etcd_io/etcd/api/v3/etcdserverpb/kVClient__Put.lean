/-
`(*etcdserverpb.kVClient).Put(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
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

/-- `c.Put(ctx, in, opts...)` on a stub on a connection to `K` (`kvStubAt`): `Invoke` of
`"/etcdserverpb.KV/Put"` with `grpc.StaticMethod()` before the options, into a new
`*PutResponse`: the call's answer (`putCallOut`, the run's `Q`); the request comes back. -/
abbrev kVClient.Put.spec : Prop :=
  ∀ (kc conn : Loc) (K : KVConn GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.PutRequest) (k v : GoString) (opts : GoSlice)
    (vs : List GoInterface) (Q : PutRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isKVConn conn K ∗ context.isContext ctx cd ∗ inp ↦ req ∗ req.Key' ↦*□ k ∗ req.Value' ↦*□ v ∗
      opts ↦*□ vs ∗ callOptsOk vs ∗ putRunOk K (putReqOp req k v) Q }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.PutRequest, inp ↦ req') ∗ putCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
