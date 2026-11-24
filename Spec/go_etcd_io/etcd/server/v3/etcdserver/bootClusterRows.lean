/-
**The cluster rows of `bootOk` that stage 2 does not prove** (claim #34, stage 2, 2026-11-25): a law
that `bootstrappedCluster.Finalize.wp_proof` takes, specified here and not proved, a hypothesis of
the results that reach it (`?` in the server's link). Not a Go function. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The new cluster's `Members()` stays its boot members, and its names-only apply rows hold**
(a law, not proved; until stage 2, 2026-11-25, these two rows were trusted clauses of `bootOk`,
`Hmembers` and `Hisc`, and the whole of `Finalize.spec`'s post was a hypothesis): of the cluster `c`
as `Finalize` leaves it (its lock, `membership.isRaftCluster`; its id `bootGo.cid`; the apply
thread's half of its members, `bootGo.memMap`), `srvMembersDir c ps dir` (every later `Members()`
answers the boot members, in `ps` order, with the directory's URLs, which parse,
`membership.peerURLsOk`) and `clusterApplyRest c` (the rows of the names-only `SetVersion`,
`UpdateAttributes`, `SetDowngradeInfo`). Why it is open: the first needs the lock invariant to carry a
property of its members (plan §7.1 I5, kept by `AddMember`, `UpdateAttributes` and `Recover`) and
`peerURLsOk` defined; the second needs those three methods translated and proved. -/
abbrev bootClusterRows.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (c : Loc),
  bootGo.membersOk cfg U → c ≠ null →
  membership.isRaftCluster (GF := GF) c ∗
    membership.clusterCid c (bootGo.cid U cfg.InitialClusterToken') ∗
    membership.clusterMem c (bootGo.memMap U cfg.InitialClusterToken') ⊢
  membership.clusterMem c (bootGo.memMap U cfg.InitialClusterToken') ∗
    srvMembersDir c (bootGo.ps U cfg.InitialClusterToken') (bootGo.dir U cfg.InitialClusterToken') ∗
    clusterApplyRest c

end spec

end EtcdGrove
end Perennial
