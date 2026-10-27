/-
**The Election service's server's contracts** (the auth plan's A3c, 2026-10-24;
`notes/decisions.md`, "A3c of the auth plan: Lock and Election"). Lean-first (no Rocq
counterpart).

The server (`v3election.electionServer`, `election.go`) holds a `*clientv3.Client`, in etcd the
in-process client `v3client.New(s)` (untranslated here). Its handlers make only client calls: a
session over the request's lease (`session`), and an election on the request's name
(`NewElection`, `Campaign`, `Leader`) or a resumed one on the request's leader key
(`ResumeElection`, `Proclaim`, `Resign`): the client's `concurrency` package, proved. So its specs
are stated over what they need of that client, a hypothesis (axiom-free): `electionClientOk`, the
session's client contract and, for every prefix, the election's (`isEtcdMutexClient`). Each
handler's class is that of the requests those calls send: KV requests on keys under `name/` (a
campaign, the leader's lookup), or on the request's leader key (a proclamation, a resignation), and
the lease's, as the context's principal.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Base
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvElection
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3election

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3election

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-- **The server's client**: `NewSession`'s client contract and, for every prefix, the
election's (persistent; the Lock server's `lockClientOk`). -/
abbrev electionClientOk (c : Loc) : IProp GF := v3lock.lockClientOk c

/-- **An election server** `es` over the client `c` (read-only). -/
def isElectionServer (es c : Loc) : IProp GF :=
  iprop(structFieldRef electionServer go!"c" es ↦□ c)

instance isElectionServer_persistent (es c : Loc) : Persistent (isElectionServer (GF := GF) es c) := by
  unfold isElectionServer; infer_instance

/-- **A request's leader key** `lk` (read-only): its name, key, revision and lease. -/
def leaderKeyAt (lk : Loc) (name key : GoString) (rev lease : w64) : IProp GF :=
  iprop(∃ nsl ksl : GoSlice, structFieldRef v3electionpb.LeaderKey go!"Name" lk ↦□ nsl ∗
    nsl ↦*□ name ∗ structFieldRef v3electionpb.LeaderKey go!"Key" lk ↦□ ksl ∗ ksl ↦*□ key ∗
    structFieldRef v3electionpb.LeaderKey go!"Rev" lk ↦□ rev ∗
    structFieldRef v3electionpb.LeaderKey go!"Lease" lk ↦□ lease)

instance leaderKeyAt_persistent (lk : Loc) (name key : GoString) (rev lease : w64) :
    Persistent (leaderKeyAt (GF := GF) lk name key rev lease) := by
  unfold leaderKeyAt; infer_instance

/-- The options of the server's session over `lease` with the context `ctx` (`session`). -/
def sessOpts (cctx : GoInterface) (lease : w64) (ctx : GoInterfaceOk) : SessionOpts :=
  sessOptsFold [withLeaseSM lease, withContextM (GoInterface.ok ctx)] (SessionOpts.init cctx)

end defs

end v3election
end EtcdGrove
end Perennial
