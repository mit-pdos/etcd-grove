/-
## `NewMemberAsLearner(name, peerURLs, clusterName, now)` (`member.go:51-61`): names only

**Users.** 2a's `ClusterServer.MemberAdd` (with `time.Now()`), `NewClusterFromURLsMap` (with `nil`);
`ReqJoin`. **Why it is true.** `computeMemberID` (SHA-1 of the sorted URL strings, the token and,
with `now`, its Unix seconds: `memberIdOf` without it), a member with the name, the URL strings, no
client URL. **Changes**: new (round 1, completeness F3/F4). **Margin.** With `now`, the id is not
named (some `uint64`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.config.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Membership

open Iris Iris.BI EtcdModel Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

/-- **A new member record** (a learner). -/
def NewMemberAsLearner.spec : Prop :=
  ∀ (name : GoString) (sl : GoSlice) (urls : List GoString) (token : GoString) (now : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ Types.urlsStrs sl urls }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewMemberAsLearner)) (Val #name)) (Val #sl)) (Val #token)) (Val #now))
  {{ (p : Loc), RET #p; ∃ id : Nat, ⌜id < 2 ^ 64 ∧ (now = null → id = memberIdOf urls token)⌝ ∗
      memberPts p (DFrac.own 1)
        { id := id, name := name, peerURLs := urls, clientURLs := [], isLearner := true } }}

end spec

end Membership
end EtcdGrove
end Perennial
