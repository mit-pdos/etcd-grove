/-
`kubernetes.Client.OptimisticDelete(ctx, key, expectedRevision, opts)`
(`client/v3/kubernetes/client.go`; phase 3 of `notes/k8s-etcd3-plan.md`). Lean-first (no Rocq
counterpart).

`k.KV.Txn(ctx).If(ModRevision(key) = expectedRevision).Then(OpDelete(key))`,
and `.Else(OpGet(key))` with `GetOnFailure`, committed through `New`'s client of the members `ms`
configured to send a write at most once (`clientWriteOnce`), with an update fired at most once at
each member (`kvOpAu1`, as linkvtxn's `callTxn`): linkv's transaction `txnOf [.mod key rev]
[.del key] (g ? [.get key] : [])`. The answer is about the state `σ` the update fired at
(`Q σ`): `Succeeded` the server's verdict there, `Revision` the state's after the transaction,
and with `GetOnFailure`, on a failed comparison, `KV` the key's key-value (`nil` if none). Or an
error (the update fired at most once). Unlike `OptimisticPut`, the Go code indexes
`txnResp.Responses[0]` without checking its length; the server's answer always has it
(`failure_resps`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev Client.OptimisticDelete.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (rev : w64)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.DeleteOptions) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce kc.Client' (ms.map client.SrvAt.addr) ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.txn (optDelTxn key rev opts.GetOnFailure')) Q) }}
    (App (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!!
      go!"OptimisticDelete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #rev)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.DeleteResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, Q σ ∗
        ⌜resp.Succeeded' = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
            (optDelTxn key rev opts.GetOnFailure')).1 ∧
          resp.Revision' =
            W64 ((kvOpStep (.txn (optDelTxn key rev opts.GetOnFailure')) σ).rev : Int) ∧
          σ.rev + 3 < 2 ^ 63⌝ ∗
        (if opts.GetOnFailure' && !resp.Succeeded' then
          kvOut resp.KV' (single (σ.kvs.filter fun v => decide (v.key = key)))
        else iprop(⌜resp.KV' = null⌝))) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end kubernetes
end EtcdGrove
end Perennial
