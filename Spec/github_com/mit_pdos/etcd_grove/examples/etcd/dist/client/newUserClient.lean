/-
`newUserClient(addr, name, pw)` (`examples/etcd/dist/client/auth.go`; authN's, copied): `clientv3.New` of the one
endpoint `addr`, authenticating as `name` with password `pw`, with no proxy. Over `etcd_dist.authd.New_user_dist`
(auth on, at the cluster view `Γ`): on success the client `userCli cl addr V cfg` (`AuthLeaseDefs.lean`) whose
principal is `name`; the auth-on contracts' client facts follow from it at the member the caller names
(`userClientAt_of_userCli`, `leaseUserAt_of_userCli`). The password check `New_user_dist` reports is dropped (no
caller reads it). Lean-first (no Rocq counterpart); F7 stage S4.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist etcd_dist.authd

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `newUserClient(addr, name, pw)`, auth on, `addr` serving a member of the view: `nil` and a user client
of `addr` (`userCli`) whose principal is `name`; or an error and `null`. -/
abbrev newUserClient.spec : Prop :=
  ∀ [π : NetProtoGS] (addr name pw : GoString) (V : WEnv GF) (Γ : DistView),
  threadBound GF ≤ 2 ^ 30 → plainEndpoint addr → strsSizeOk [name, pw] →
  name ≠ go!"" → pw ≠ go!"" →
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → Γ.auth = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ membersAt (Gg := hG.goose_globalGS) [addr] Γ }}
    (App (App (App (Val (@! client.newUserClient)) (Val #addr)) (Val #name)) (Val #pw))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ cfg : go_etcd_io.etcd.client.v3.Config,
          userCli cl addr V cfg ∗ ⌜principalOf cfg = some name⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ cl = null⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
