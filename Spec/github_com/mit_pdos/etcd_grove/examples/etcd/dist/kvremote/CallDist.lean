/- Lean-first (no Rocq counterpart).

`txnlin.Call(cli, input)` **across machines** (`examples/lib/txnwork/linkvtxn.go`): the call a kv
client machine makes (`kvremote.Node`'s operation), through its own clientv3 client of the cluster's
endpoints. txnlin's `Call.spec` with the in-process servers' registrations (`isNewClient ∗
clientWriteOnce ∗ [∗list] kvRegsAt`, one update per member) replaced by the cluster view's client
facts, `kvClientAt cl api eps V Γ` (N2's drafts, `dist/ClientViewDist.lean`: `New`'s client `cl` of
the endpoints `eps`, its `KV` field the `*kv` `api`, every endpoint a member of the view `Γ`), and one
update at the cluster's KV names `Γ.kv` (`callUpd`). The post is `Call.spec`'s: the failed call's output
(`errOut`), or a successful one at the state `σ` the update fired at (`callRes`), the model's answer at
`σ` when `σ` is good, `σ`'s revision fitting a word. For a cluster with auth off (`Γ.auth = false`: the
table has etcd's KV entries, flagged as never refusing, for an auth-off view; a write is sent at most once).

Proved in `Proof/.../dist/kvremote/CallDist.lean` over the client calls' laws (`ClientCallDistLaws.lean`,
proved from the client's specs at the client's `isKv` of the view, stage B′).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Calls
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlin

open Iris Iris.BI Net github_com.mit_pdos.etcd_grove.examples.lib.txnwork
open EtcdGrove.etcd_dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev Call_dist.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
    (cl api : Loc) (eps : List GoString) (V : client.WEnv GF) (Γ : DistView),
  Γ.auth = false →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (x : Input) (i : MI) (Q : KVState → IProp GF), decIn x = some i → GenIn x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      kvClientAt cl api eps V Γ ∗ callUpd Γ.kv i Q }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.txnwork.Call)) (Val #cl))
      (Val #(boxIn x)))
  {{ (v : GoInterface), RET #v; levelTok 0 ∗ (⌜v = boxOut errOut⌝ ∨
      ∃ (y : Output) (σ : KVState), callRes i Q σ ∗
        ⌜v = boxOut y ∧ y.Err' = false ∧ kvRevFits σ.rev ∧ (GoodKV σ → y = outAt i σ)⌝) }}

end spec

end etcd_txnlin
end EtcdGrove
end Perennial
