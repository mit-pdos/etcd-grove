/- Lean-first (no Rocq counterpart).

**DRAFT (etcd_safe S0, 2026-11-26; unreached, not reviewed).** `etcdserver.NewServer` on a member machine of a
distributed deployment, restarted on its files: an interim trust-boundary axiom until phase 7 S5 across machines
and `NewServer.wp_proofC` (`notes/etcd-dist-plan.md`, "Interim transport"; `plans/etcd-safe-restart-design.md` §3).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.NewServerCDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewServer(cfg)` restarted on a member machine's files** (DRAFT, interim trust boundary; the spec's file
header lists what changes from `NewServer.specC`).

**Contract.** On a data directory a crash or a graceful stop left (`srvCrashImageAt`), with every other peer's
directory address set to etcd's peer protocols of the cluster (`httpAddrAt`) and no HTTP proxy variable set
(`noProxyEnv`), `NewServer` returns `specC`'s post at network names `γn` with the in-process network's payload
(`srvNet γ`) and directory; the threads it starts (rafthttp's transport, the raft node, the lessor) neither get
stuck nor panic.

**Why it is true.** It is `NewServer_dist.wp_proof`'s argument at a restart. The in-process `NewServer.specC`
(`NewServer.wp_proofC`, proved over `specRAt` but for one `sorry`, `NewServerCrash.lean:81`) states the
construction over the in-process network; across machines only the transport's round trips change, which go to
the other members' peer addresses, set by the start to `httpPeerSvc` (`http_addr_set`) and served by the other
members' peer handlers (`PeerServe_dist`), each fact indexed by the cluster `γ.cl` (`httpAddrAt` reads `γ` only
through `γ.cl`, so the restart's registry name `γ.reg` does not matter). A restart contacts no peer during
`bootstrap` (`bootstrapClusterWithWAL`: no `isMemberBootstrapped`), so the bootstrap contract is the in-process
crash contract (`bootstrapCrashContract`) unchanged. The proxy and the stray listener at a peer address are as in
`NewServer_dist`'s docstring. A duplicate of the member is excluded by the image's exclusive `raftState γ.cl id S`
and vacancy (`srvCrashImageAt`).

**Scope.** Auth off and no compaction mode (`specC`'s): the classes `etcd_safe` closes first (design D4).

**Retired by** phase 7 S5 (as `NewServer_dist`) with `NewServer.wp_proofC` finished and restated over S5's
address facts.

**Route.** Translate: etcd's server is translated; rafthttp across machines needs net/http's client over the net
extension (phase 7 S5), not yet. Go model: none (the transport is etcd's own code). Trusted code: none. Axiom:
interim, as `NewServer_dist`. -/
axiom NewServerC_dist.wp_proof [π : NetProtoGS] : NewServer.specC_dist (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
