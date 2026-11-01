/-
`(*clientv3.retryKVClient).Compact(ctx, in, opts...)` (`client/v3/retry.go`, translated for the client's `kv.Compact`, 2026-11-01). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

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

/-- `rkv.Compact(ctx, in, opts...)` on a `retryKVClient` over the connection `conn`
(`retryKVAt`): the stub's `Compact` with the same options (no retry policy added: the default,
`nonRepeatable`), as `retryKVClient.Put`. (The client's `kv.Compact`, 2026-11-01.) -/
abbrev retryKVClient.Compact.spec : Prop :=
  ∀ (rkv conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbCompactionRequest pbCompactionResponse)
    (Q : CompactRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.CompactionRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVAt rkv conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/Compact" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Compact" addr vs
        (attemptPre conn (GoInterface.ok ctx) Spec ⟨req.Revision', req.Physical'⟩ Q) ∗
      ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝ }}
    (App (App (App (Val (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!!
        go!"Compact")) (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.CompactionRequest, inp ↦ req') ∗ compactCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
