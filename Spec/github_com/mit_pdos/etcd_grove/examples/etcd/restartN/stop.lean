/-
`stop(s, k)` (`examples/etcd/restartN/restartN.go`; restart3's `stop` with the member count `k` an
argument): the wait until the member applied the cluster's bootstrap log (`AppliedIndex() ≥ k`, one
entry per member),
then `s.HardStop()`. Lean-first (no Rocq counterpart).

**The triple:** from the applied index's invariant (`srvAppliedInv`), the server's data directory
(`srvDataDir`, `name ++ ".etcd"`), the right to stop it (`srvStopRight`, at an apply environment in the
stop's scope) and its unused serving readers (`srvStopReaders`), of a cluster whose bootstrap log has
at most `k` entries: the member's data directory as the stop left it, at the request names `ρ`
(`srvDiskImage`), as its restart bundle without addresses (`etcdstart.memberRestartRes`; its peer
address stays served by its `raftSwap`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- See the file header. -/
abbrev stop.spec : Prop :=
  ∀ (s : Loc) (E Ea : apply.AEnv GF) (ρ : ReqNames) (id : w64) (dd : GoString)
    (γn : NetNames GF) (name : GoString) (k : w64),
  ρ.rd.raft.raft.boot.length ≤ uint.nat k → srvStop.scope E →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      srvAppliedInv s Ea ρ.rd ∗ srvDataDir s (name ++ go!".etcd") ∗
      srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.stop)) (Val #s)) (Val #k))
  {{ RET #(); etcdstart.memberRestartRes name {} γn ρ.rd.raft.raft ρ id }}

end spec

end etcd_restartN
end EtcdGrove
end Perennial
