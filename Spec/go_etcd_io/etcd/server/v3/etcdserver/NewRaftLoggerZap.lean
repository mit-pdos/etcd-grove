/-
`NewRaftLoggerZap(lg)` (`zap_raft.go` at the etcd pin `edc800c6f`: `&zapRaftLogger{lg: lg, sugar:
lg.Sugar()}` as a `raft.Logger`). Claim #34, stage 4 (2026-11-25). Lean-first.

**Not proved: the trust-boundary axiom** `NewRaftLoggerZap.wp_proof` (`Proof/.../NewRaftLoggerZap.lean`;
premises to axioms, item C, 2026-11-24: until then the closed theorems took the weaker premise
`rnLoggerZapOk`, any interface, no contract; claim #34 then stated this stronger triple as a hypothesis of
`raftConfig`): etcd's `zap_raft.go` and zap's `SugaredLogger` are names-only. It holds of Go for a logger
as `zap.NewNop()` builds it (`zapLoggerOk`, the only kind this repository's specs give): the body is
`skipCallerLg := lg.WithOptions(zap.AddCallerSkip(1)); return &zapRaftLogger{lg: skipCallerLg, sugar:
skipCallerLg.Sugar()}` (`WithOptions` and `Sugar` clone the non-nil logger, keeping its core);
`zapRaftLogger`'s `Infof`, `Debugf`, `Warningf`, `Errorf` call the sugared logger's, whose `log` returns at
once when the core (`nopCore`) is not enabled at the level (zap v1.28.0 `sugar.go`, `log`: `lvl <
DPanicLevel && !s.base.Core().Enabled(lvl)`), so each returns with no effect: `isLogger` (raft's logger
contract). Interim: retired once zap's `WithOptions`, `AddCallerSkip` and `Sugar` have specs and the body
is translated (plan item C, claim #40).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootParts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev NewRaftLoggerZap.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ zapLoggerOk lg }}
    (App (Val (@! NewRaftLoggerZap)) (Val #lg))
  {{ (l : GoInterface), RET #l; ∃ lok : GoInterfaceOk, ⌜l = interface.ok lok⌝ ∗ isLogger lok }}

end spec

end EtcdGrove
end Perennial
