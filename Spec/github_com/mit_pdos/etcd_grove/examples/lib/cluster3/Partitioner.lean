/-
`Partitioner(srvs, brs, sched)` (`examples/lib/cluster3/cluster3.go`, until 2026-11-05 package `partition`'s; the partition plan's S3a,
2026-10-20; the client steps since 2026-10-21, `notes/client-cut-plan.md`): for each step of the
schedule `sched`, after its delay (`time.Sleep`), a peer step (`PeerStep`: cut or mend the link
between members `A` and `B` of `srvs`) or a client step (`ClientStep`: blackhole, unblackhole or
drop the connections of member `A`'s bridge in `brs`, a second blackhole skipped), by its kind;
any other kind does nothing. Lean-first (no Rocq counterpart).

**The triple:** over the read-only slices of servers `ss`, each a member of the network `γn` with
one of its transport's reader tokens (`etcdstart.srvPeerCtl`; 2026-10-24, rafthttp stage 6d), of bridges `bs`, each owned and not blackholed (`ownBridge`), and of steps: it
returns. Nothing is assumed of the schedule: the theorems that run it (partition's `Main`) quantify over
every one.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- See the file header. -/
abbrev Partitioner.spec : Prop :=
  PeerPausable →
  ∀ (γn : NetNames GF) (srvs brs sched : GoSlice) (ss : List Loc) (bs : List GoInterface)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 ∗
      srvs ↦*□ ss ∗ brs ↦*□ bs ∗ sched ↦*□ steps ∗
      ([∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
      ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner))
      (Val #srvs)) (Val #brs)) (Val #sched))
  {{ RET #(); True }}

end spec

end cluster3
end EtcdGrove
end Perennial
