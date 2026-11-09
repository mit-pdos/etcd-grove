/-
`concurrency.NewElection(s, pfx)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippets: `concurrency/election.go`.

Proof sketch: the struct allocated; `session` and `keyPrefix` persisted (`isElection`).

Changes: from `specs-ref`'s `NewElection.lean`: no client premise (only stores).

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

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

/-- `NewElection(s, pfx)`: an election on the prefix `pfx + "/"`, not leading. -/
def NewElection.spec : Prop :=
  ∀ (s : Loc) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewElection)) (Val #s)) (Val #pfx))
  {{ (e : Loc), RET #e; isElection e s (pfx ++ go!"/") ∗
      electionSt e { leaderKey := [], leaderRev := W64 0, leaderSession := null, hdr := null } }}

end spec

end Concurrency
end EtcdGrove
end Perennial
