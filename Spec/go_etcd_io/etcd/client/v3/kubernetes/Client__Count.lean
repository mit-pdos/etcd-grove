/-
`kubernetes.Client.Count(ctx, prefix, opts)` (`client/v3/kubernetes/client.go`; PR `etcd-io/etcd#21209`).
Lean-first (no Rocq counterpart).

`k.KV.Get(ctx, prefix, WithPrefix(), WithCountOnly())` through `New`'s client of the members `ms`
(`isNewClient`, failover: each attempt to one of them), with a read update or none at each member.
The answer is about the state `σ` the update fired at (`□ Q σ`): the number of keys in
`[prefixStart prefix, prefixRangeEnd prefix)` (`prefixStart` is `"\x00"` when `prefix` is empty and
`prefix` otherwise). Or `0` and an error of the client (`clientErr`, `statusErrOk`).
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
abbrev Client.Count.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (pfx : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.CountOptions) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      □ ([∧list] x ∈ ms, ⌜Q = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv Q) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Count"))
      (Val #(GoInterface.ok ci))) (Val #pfx)) (Val #opts))
  {{ (cnt : w64) (err : GoInterface),
      RET (PairV #cnt #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q σ ∗
        ⌜cnt =
          W64 (((σ.kvs.filter (fun v => inRange (prefixStart pfx) (prefixRangeEnd pfx) v.key)).length : Int)) ∧
          σ.rev + 3 < 2 ^ 63⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ cnt = W64 0⌝ ∗ ⌜clientErr err⌝ ∗
        go_etcd_io.etcd.cache.v3.statusErrOk err }}

end spec

end kubernetes
end EtcdGrove
end Perennial
