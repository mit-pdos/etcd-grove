/-
`kubernetes.Client.OptimisticPut(ctx, key, value, expectedRevision, opts)`
(`client/v3/kubernetes/client.go`; phase 3 of `notes/k8s-etcd3-plan.md`). Lean-first (no Rocq
counterpart).

`k.KV.Txn(ctx).If(ModRevision(key) = expectedRevision).Then(OpPut(key, value, WithLease(0)))`,
and `.Else(OpGet(key))` with `GetOnFailure`, committed through `New`'s client of the members `ms`
configured to send a write at most once (`clientWriteOnce`), with an update fired at most once at
each member (`kvOpAu1`, as linkvtxn's `callTxn`): linkv's transaction `txnOf [.mod key rev]
[.put key val] (g ? [.get key] : [])`. The answer is about the state `σ` the update fired at
(`Q σ`): `Succeeded` the server's verdict there, `Revision` the state's after the transaction,
and with `GetOnFailure`, on a failed comparison, `KV` the key's key-value (`nil` if none). Or an
error of the client (`clientErr`, `statusErrOk`: its `Error()` returns some string; the update fired at most once). The lease is `0` (the store's configuration, D30d).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev Client.OptimisticPut.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client) (ms : List (client.SrvAt GF))
    (V : client.WEnv GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (vsl : GoSlice) (val : GoString) (rev : w64)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.PutOptions) (Q : KVState → IProp GF),
  opts.LeaseID' = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      client.clientWriteOnce kc.Client' (ms.map client.SrvAt.addr) ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ vsl ↦*□ val ∗
      ([∧list] x ∈ ms, kvOpAu1 x.γr.kv (.txn (optPutTxn key val rev opts.GetOnFailure')) Q) }}
    (App (App (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!!
      go!"OptimisticPut")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #vsl)) (Val #rev))
      (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.PutResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, Q σ ∗
        ⌜resp.Succeeded' = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
            (optPutTxn key val rev opts.GetOnFailure')).1 ∧
          resp.Revision' =
            W64 ((kvOpStep (.txn (optPutTxn key val rev opts.GetOnFailure')) σ).rev : Int) ∧
          σ.rev + 3 < 2 ^ 63⌝ ∗
        (if opts.GetOnFailure' && !resp.Succeeded' then
          kvOut resp.KV' (single (σ.kvs.filter fun v => decide (v.key = key)))
        else iprop(⌜resp.KV' = null⌝))) ∨
      ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err }}

end spec

end kubernetes
end EtcdGrove
end Perennial
