/-
`kubernetes.Client.Get(ctx, key, opts)` (`client/v3/kubernetes/client.go`; phase 3 of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

`k.KV.Get(ctx, key, WithRev(opts.Revision), WithLimit(1))` through `New`'s client of the members
`ms` (`isNewClient`, failover: each attempt to one of them), at the latest revision
(`opts.Revision' = 0`: the only revision the server's specs serve, and the one the store's unary
paths pass, `GetOptions{}`), with a read update or none at each member, as linkvtxn's
`client_Get_st`. The answer is about the state `σ` the update fired at (`□ Q σ`): its revision is
the response's, and its key-value of `key` the response's `KV` (`nil` if there is none). Or an
error of the client (`clientErr`, `statusErrOk`: its `Error()` returns some string;
`errCellOk`: no caller's `errors.New` value, D37).

**The update knows the response** (D30n, 2026-10-23): `Get` prophesies its response's revision
and the key's mod revision (`0` if absent; the fork's ghost-only `ResolveU64`s), so the caller's
read update may depend on them (`Q R m`): at every state it fires at, it knows the revision `R`
and the key's mod revision `m` of the state the response will reflect (`modAt`). `Get` makes the
update once, at the prophesied pair (the precondition's `∀ R m, |==> …` is used once), and the
answer is `Q` at the response's own pair, so a caller can commit once, at a state with that pair.
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

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

/-- A key's mod revision in a state, `0` if absent. -/
def modAt [GooseExts] (key : GoString) (σ : KVState) : w64 :=
  ((mvcc.findKey key σ.kvs).map EtcdKv.modRev).getD (W64 0)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.kubernetes.Assumptions]

/-- See the file header. -/
abbrev Client.Get.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (kc : go_etcd_io.etcd.client.v3.kubernetes.Client)
    (ms : List (client.SrvAt GF)) (V : client.WEnv GF) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString)
    (opts : go_etcd_io.etcd.client.v3.kubernetes.GetOptions) (Q : w64 → w64 → KVState → IProp GF),
  opts.Revision' = W64 0 → key.length ≤ 2 ^ 27 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient kc.Client' (ms.map client.SrvAt.addr) V ∗
      ([∗list] x ∈ ms, client.kvRegsAt x) ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗
      (∀ R m, |==> □ [∧list] x ∈ ms, ⌜Q R m = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv (Q R m)) }}
    (App (App (App (Val (kc @!! go_etcd_io.etcd.client.v3.kubernetes.Client.ty @!! go!"Get"))
      (Val #(GoInterface.ok ci))) (Val #key)) (Val #opts))
  {{ (resp : go_etcd_io.etcd.client.v3.kubernetes.GetResponse) (err : GoInterface),
      RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ : KVState, □ Q (W64 (σ.rev : Int)) (modAt key σ) σ ∗
        ⌜resp.Revision' = W64 (σ.rev : Int) ∧ σ.rev + 3 < 2 ^ 63⌝ ∗
        kvOut resp.KV' (mvcc.findKey key σ.kvs)) ∨
      ⌜err ≠ GoInterface.nil⌝ ∗ ⌜clientErr err⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
        go_etcd_io.etcd.cache.v3.errCellOk err }}

end spec

end kubernetes
end EtcdGrove
end Perennial
