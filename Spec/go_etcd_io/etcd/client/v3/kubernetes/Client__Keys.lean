/-
`kubernetes.Client.Keys(ctx, prefix, opts)` (`client/v3/kubernetes/client.go`; PR `etcd-io/etcd#21209`).
Lean-first (no Rocq counterpart).

`k.KV.Get(ctx, prefix, WithRange(GetPrefixRangeEnd(prefix)), WithKeysOnly(), WithRev(opts.Revision))`
through `New`'s client of the members `ms` (`isNewClient`, failover: each attempt to one of them),
at the latest revision (`opts.Revision' = 0`), with a read update or none at each member. The
answer is about the state `σ` the update fired at (`□ Q σ`): its revision is `resp.Revision`, the
number of keys in `[prefix, prefixRangeEnd prefix)` is `resp.Count`, and the keys of `[prefix,
prefixRangeEnd prefix)` in order are `resp.Keys` (`keysSlice`). Or an error of the client
(`clientErr`, `statusErrOk`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Defs
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Base
public import GeneratedProof.go_etcd_io.etcd.client.v3.kubernetes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kubernetes

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev Client.Keys.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (pfx : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.KeysOptions) (Q : KVState → IProp GF),
  opts.Revision' = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Keys"))
      (Val #(GoInterface.ok ci))) (Val #pfx)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.KeysResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q σ ∗
        ⌜resp.Revision' = W64 (σ.rev : Int) ∧
          resp.Count' =
            W64 (((σ.kvs.filter (fun v => inRange pfx (prefixRangeEnd pfx) v.key)).length : Int)) ∧
          σ.rev + 3 < 2 ^ 63⌝ ∗
        keysSlice resp.Keys'
          ((σ.kvs.filter (fun v => inRange pfx (prefixRangeEnd pfx) v.key)).map EtcdKv.key)) ∨
      ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err }}

end spec

end kubernetes
end EtcdGrove
end Perennial
