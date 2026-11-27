/-
`newClient(eps)`: `etcdstart.NewClients(eps, zap.NewNop())` (`examples/etcd/dist/client/client.go`).
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.LeaseDefs
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
      ((⌜err = GoInterface.nil⌝ ∗ isNewClient cl addrs V ∗ clientNoProxy cl ∗
        -- (F7 S5, 2026-11-26) the anonymous client: no token, user or password (`NewClients`')
        ∃ cfg : go_etcd_io.etcd.client.v3.Config, clientF cl go!"cfg" ↦□ cfg ∗
          ⌜cfg.Token' = [] ∧ cfg.Username' = go!"" ∧ cfg.Password' = go!""⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
