/-
`stop(s)` (`examples/etcd/restart1/restart1.go`; restart S7.5, step e, 2026-11-14): the wait until the
member applied the bootstrap log (`AppliedIndex() ≥ NBoot`), then `s.HardStop()`. Lean-first (no Rocq
counterpart). restart3's `stop` without the peer listener.

**The triple:** from the applied index's invariant (`srvAppliedInv`), the server's data directory
(`srvDataDir`, `restart1.etcd`), the right to stop it (`srvStopRight`, at an apply environment in the
stop's scope) and its unused serving readers (`srvStopReaders`), of a cluster whose bootstrap log has
at most `NBoot` entries: the member's data directory as the stop left it, at the request names `ρ`
(`srvDiskImage`), as its restart bundle without addresses (`etcdstart.memberRestartRes`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- See the file header. -/
abbrev stop.spec : Prop :=
  ∀ (s : Loc) (E Ea : apply.AEnv GF) (ρ : ReqNames) (id : w64) (dd : GoString)
    (γn : NetNames GF),
  ρ.rd.raft.raft.boot.length ≤ 1 → srvStop.scope E →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 ∗
      srvAppliedInv s Ea ρ.rd ∗ srvDataDir s (name ++ go!".etcd") ∗
      srvStopRight s E ρ.rd.raft.raft ρ id dd ∗ srvStopReaders E }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.stop)) (Val #s))
  {{ RET #(); etcdstart.memberRestartRes name {} γn ρ.rd.raft.raft ρ id }}

end spec

end etcd_restart1
end EtcdGrove
end Perennial
