/-
`stop(s)` (`examples/etcd/restart/restart3.go`; restart3 C2, 2026-11-15, restart1's `stop`): the wait
until the member applied the cluster's bootstrap log (`AppliedIndex() ≥ NBoot`, one entry per member),
then `s.HardStop()`. Lean-first (no Rocq counterpart).

**The triple:** from the applied index's invariant (`srvAppliedInv`), the server's data directory
(`srvDataDir`, `memberDataDir name`), the right to stop it (`srvStopRight`, at an apply environment in the
stop's scope) and its unused serving readers (`srvStopReaders`), of a cluster whose bootstrap log has
at most `NBoot = 3` entries: the member's data directory as the stop left it, at the request names `ρ`
(`srvDiskImage`), as its restart bundle without addresses (`etcdstart.memberRestartRes`; its peer
address stays served by its `raftSwap`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev stop.spec : Prop :=
  ∀ (s : Loc) (E Ea : apply.AEnv GF) (ρ : ReqNames) (id : w64) (dd : GoString)
    (γn : NetNames GF) (name : GoString),
  ρ.rd.raft.raft.boot.length ≤ 3 → srvStop.scope E →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      srvAppliedInv s Ea ρ.rd ∗ srvDataDir s (memberDataDir name) ∗
      srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.stop)) (Val #s))
  {{ RET #(); etcdstart.memberRestartRes name {} γn ρ.rd.raft.raft ρ id }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
