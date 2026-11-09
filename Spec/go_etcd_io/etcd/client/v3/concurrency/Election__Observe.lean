/-
`(*concurrency.Election).Observe(ctx)` (`client/v3/concurrency/election.go`).

Users: `server/etcdserver/api/v3election/election.go` (`Campaign`:45 a new election, `Campaign`,
then `Header()`, `Key()`, `Rev()` and the lease returned as the leader key; `Proclaim`:68 and
`Resign`:118 on `ResumeElection(s, name, key, rev)` from the remote client's leader key;
`Leader`:103 and `Observe`:80 on a new election, sessions with lease `-1`), etcdctl's `elect`
command (not in the pinned sources), etcd's tests
(`tests/integration/clientv3/concurrency/election_test.go`, `example_election_test.go`). Snippet: `concurrency/election.go` (`ReqObserve`).

Proof sketch: an unbuffered channel (Perennial's SPSC idiom: `observeAt` the consumer,
`observeProd` the producer), `go e.observe(ctx, ch)` (`wp_fork`, the `threadTok`,
`Election.observe.spec`).

Changes: from `specs-ref`'s `Election__Observe.lean`: over the cluster's history (`ObservedAt`)
instead of the old three-case `observedAt`; the consumer's header revisions non-decreasing.

Margin: etcd's watch is gap-free, so each observed value is the leader's at its revision (present
there) except when one revision both puts and deletes the key (nested transactions); stated as
`ObservedAt` (written at its revision, nothing older then). Liveness (the most recent leader is
eventually posted) is not stated.
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

/-- `e.Observe(ctx)`: a channel whose consumer (`observeAt`) receives the leader's values, each
written by the prefix's oldest key at a revision the cluster reached, in header order; closed when
`ctx` is done or a watch fails. -/
def Election.Observe.spec : Prop :=
  ∀ (e s : Loc) (pfx : GoString) (γ : Cluster) (who : Principal) (id : w64)
    (ctx : GoInterface) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isElection e s pfx ∗ isSession s γ who id ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ etcdPerm γ T ∗ ⌜effIn readEff T⌝ ∗
      threadTok }}
    (App (Val (e @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.concurrency.Election.ty @!! go!"Observe")) (Val #ctx))
  {{ (ch : GoChan), RET #ch; observeAt ch γ pfx 0 }}

end spec

end Concurrency
end EtcdGrove
end Perennial
