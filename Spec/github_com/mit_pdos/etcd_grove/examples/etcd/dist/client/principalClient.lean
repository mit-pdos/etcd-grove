/-
`principalClient(eps, who)` (`examples/etcd/dist/client/nodes.go`): **a principal's client** (#50 F7 S7),
`RunAuth`'s choices: `u` and `v` as their users through `eps[1 % k]` and `eps[2 % k]` (`newUserClient`), `bad`
anonymously through `eps[1 % k]` and anyone else anonymously through `eps[0]` (`newClient`).

**The triple**: from the members' client addresses `addrs` (the slice `eps`, every address serving a member of
the auth-on view `Γ`), either `nil` and a user client `userCli cl a V cfg` of one address `a ∈ addrs` whose
principal is `who`'s (`u`, `v`) or none (the anonymous client): what `etcd_auth.Work.spec_dist` takes of its
client; or an error. Lean-first (no Rocq counterpart).
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

/-- See the file header. -/
abbrev principalClient.spec : Prop :=
  ∀ [π : NetProtoGS] (eps : GoSlice) (addrs : List GoString) (who : GoString) (V : WEnv GF) (Γ : DistView),
  threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs → addrs ≠ [] →
  (∀ a b : w64, Γ.au a = Γ.au b → a = b) → Γ.auth = true →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ eps ↦*□ addrs ∗ membersAt (Gg := hG.goose_globalGS) addrs Γ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalClient)) (Val #eps))
      (Val #who))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (cfg : go_etcd_io.etcd.client.v3.Config),
          ⌜a ∈ addrs⌝ ∗ userCli cl a V cfg ∗
          ⌜principalOf cfg = none ∨ (principalOf cfg = some who ∧ (who = go!"u" ∨ who = go!"v"))⌝) ∨
        ⌜err ≠ GoInterface.nil⌝) }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
