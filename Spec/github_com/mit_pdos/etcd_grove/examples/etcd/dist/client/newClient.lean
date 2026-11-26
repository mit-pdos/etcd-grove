/- `newClient(eps)` (`examples/etcd/dist/client/client.go`): `etcdstart.NewClients(eps, zap.NewNop())`. Lean-first (no Rocq counterpart); #50 N9a (the same statement as N9b's, `etcd-safe-n9b`). -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
/-- `newClient(eps)` for plain endpoints, read-only: the client of those endpoints (`isNewClient` at any
watch environment `V`), dialing with no proxy, and `nil`; or an error and `null` (`NewClients`'). -/
abbrev newClient.spec : Prop :=
  ∀ (eps : GoSlice) (addrs : List GoString) (V : WEnv GF),
  threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs }}
    (App (Val (@! client.newClient)) (Val #eps))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl addrs V ∗ clientNoProxy cl) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
