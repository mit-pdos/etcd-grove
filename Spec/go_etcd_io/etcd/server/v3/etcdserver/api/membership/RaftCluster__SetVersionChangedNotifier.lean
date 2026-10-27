/-
`(*membership.RaftCluster).SetVersionChangedNotifier(n)`: names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `c.SetVersionChangedNotifier(n)` records the notifier: `c.versionChanged = n`, **without the
cluster's lock** (`cluster.go`), so with the field owned (`bootstrap` gives it, the cluster not yet
shared: `bootOk`'s `Hvcn`). Until the audit's B4a (2026-10-18) the contract took only the
persistent `isRaftCluster` and said the write was under the lock, which a concurrent `SetVersion`
(which reads the field under it) would race with. -/
abbrev membership.RaftCluster.SetVersionChangedNotifier.spec : Prop :=
  ∀ (c n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      membership.isRaftCluster c ∗ ∃ v : Loc, membership.rcVersionChangedAddr c ↦ v }}
    (App (Val (c @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!!
      go!"SetVersionChangedNotifier")) (Val #n))
  {{ RET #(); membership.rcVersionChangedAddr c ↦ n }}

end spec

end EtcdGrove
end Perennial
