/-
`partitioner(srvs, brs, sched)` (`examples/etcd/partition/etcd_partition.go`; the partition plan's S3a,
2026-10-20; the client steps since 2026-10-21, `notes/client-cut-plan.md`): for each step of the
schedule `sched`, after its delay (`time.Sleep`), a peer step (`peerStep`: cut or mend the link
between members `A` and `B` of `srvs`) or a client step (`clientStep`: blackhole, unblackhole or
drop the connections of member `A`'s bridge in `brs`, a second blackhole skipped), by its kind;
any other kind does nothing. Lean-first (no Rocq counterpart).

**The triple:** over the read-only slices of servers `ss`, each a member of the network `γn` with
one of its transport's reader tokens (`etcdstart.srvPeerCtl`; 2026-10-24, rafthttp stage 6d), of bridges `bs`, each owned and not blackholed (`ownBridge`), and of steps: it
returns. Nothing is assumed of the schedule: the theorem that runs it (`Main`) quantifies over
every one.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

/-- See the file header. -/
abbrev partitioner.spec : Prop :=
  PeerPausable →
  ∀ (γn : NetNames GF) (srvs brs sched : GoSlice) (ss : List Loc) (bs : List GoInterface)
    (steps : List github_com.mit_pdos.etcd_grove.examples.etcd.partition.Step),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition ∗
      srvs ↦*□ ss ∗ brs ↦*□ bs ∗ sched ↦*□ steps ∗
      ([∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
      ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.partitioner))
      (Val #srvs)) (Val #brs)) (Val #sched))
  {{ RET #(); True }}

end spec

end etcd_partition
end EtcdGrove
end Perennial
