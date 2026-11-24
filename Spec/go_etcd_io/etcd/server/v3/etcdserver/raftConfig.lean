/-
`raftConfig(cfg, id, s)` (`bootstrap.go:584-596` at the etcd pin `edc800c6f`), with its body since claim
#34's stage 4 (2026-11-25). Lean-first; `notes/bootstrap-proof-plan.md` §7.4. Its vocabulary:
`Proof/.../etcdserver/BootParts.lean` (`raftCfgOf`).
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

/-- **`raftConfig(cfg, id, s)`**, with a zap logger: a new `*raft.Config` holding `raftCfgOf cfg id s
lok` (the member's id, the configuration's election ticks and pre-vote, the storage `s`, raft's sizes
`maxSizePerMsg`/`maxInflightMsgs`, `CheckQuorum`), whose logger `lok` is a raft logger (`isLogger`):
`NewRaftLoggerZap(cfg.Logger.Named("raft"))`. -/
abbrev raftConfig.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id : w64) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      zapLoggerOk cfg.Logger' }}
    (App (App (App (Val (@! raftConfig)) (Val #cfg)) (Val #id)) (Val #s))
  {{ (r : Loc), RET #r;
      ∃ lok : GoInterfaceOk, r ↦ raftCfgOf cfg id s lok ∗ isLogger lok }}

end spec

end EtcdGrove
end Perennial
