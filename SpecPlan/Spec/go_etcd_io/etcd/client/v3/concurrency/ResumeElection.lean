/-
`concurrency.ResumeElection(s, pfx, leaderKey, leaderRev)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippet: `concurrency/election.go` (`ReqResumedProclaim`).

Proof sketch: the struct allocated.

Changes: from `specs-ref`'s `ResumeElection.lean`: restated.

Margin: the prefix is taken as given, without the `/` `NewElection` appends (a known oddity,
`nonissues/election-campaign-key-check.md`'s notes); nothing is checked of the key and revision:
`Proclaim` and `Resign` are fenced by them.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `ResumeElection(s, pfx, key, rev)`: an election on the prefix `pfx` (as given) leading with `key` created at `rev`, as the caller claims. -/
def ResumeElection.spec : Prop :=
  ∀ (s : Loc) (pfx key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.ResumeElection)) (Val #s)) (Val #pfx)) (Val #key)) (Val #rev))
  {{ (e : Loc), RET #e; isElection e s pfx ∗
      electionSt e { leaderKey := key, leaderRev := rev, leaderSession := s, hdr := null } }}

end spec

end Concurrency
end EtcdGrove
end Perennial
