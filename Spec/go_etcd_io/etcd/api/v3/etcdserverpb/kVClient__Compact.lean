/-
`(*etcdserverpb.kVClient).Compact(ctx, in, opts...)` (`api/etcdserverpb/rpc_grpc.pb.go`, the generated
KV stub; translated for the client's `kv.Compact`, 2026-11-01). Lean-first (no Rocq counterpart).
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

/-- `c.Compact(ctx, in, opts...)` on a stub on a connection to the server at `addr` (`kvStubAt`),
for a metadata-indexed spec `Spec` the server registered for the method and the caller's `Φ` at
every metadata an attempt may deliver (`attemptPre`), as `kVClient.Put`: `Invoke` of
`"/etcdserverpb.KV/Compact"` with `grpc.StaticMethod()` before the options, into a new
`*CompactionResponse`: the call's answer (`compactCallOut`); the request comes back. (The client's
`kv.Compact`, 2026-11-01.) -/
abbrev kVClient.Compact.spec : Prop :=
  ∀ (kc conn : Loc) (addr : List GoString)
    (Spec : GrpcSpecMd (GF := GF) pbCompactionRequest pbCompactionResponse)
    (Φ : CompactRespM → IProp GF) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (inp : Loc) (req : etcdserverpb.CompactionRequest) (opts : GoSlice) (vs : List GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ kvStubAt kc conn ∗
      isEtcdConn conn addr ∗ isGrpcRpcsMd addr go!"/etcdserverpb.KV/Compact" Spec ∗
      reqPre conn go!"/etcdserverpb.KV/Compact" addr vs
        (attemptPre conn (GoInterface.ok ctx) Spec ⟨req.Revision', req.Physical'⟩ Φ) ∗
      ctxOk ctx cd ∗ inp ↦ req ∗ opts ↦*□ vs ∗ callOptsOk vs ∗
      ⌜req.unknownFields' = slice.nil⌝ }}
    (App (App (App (Val (kc @!! go.GoType.PointerType etcdserverpb.kVClient.ty @!! go!"Compact"))
      (Val #(GoInterface.ok ctx))) (Val #inp)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (∃ req' : etcdserverpb.CompactionRequest, inp ↦ req') ∗ compactCallOut Φ resp err }}

end spec

end EtcdGrove
end Perennial
