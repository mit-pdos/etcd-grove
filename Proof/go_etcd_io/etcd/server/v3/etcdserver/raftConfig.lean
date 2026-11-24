/-
The proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftConfig.lean` (claim #34, stage 4,
2026-11-25): the configuration's literal, over zap's `Logger.Named` and `NewRaftLoggerZap`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftConfig
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewRaftLoggerZap
public import Spec.go_uber_org.zap.Logger__Named

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem raftConfig.wp_proof
    (hNamed : zap.Logger.Named.spec (GF := GF) (hG := hG))
    (hNRL : NewRaftLoggerZap.spec (GF := GF) (hG := hG)) :
    raftConfig.spec (GF := GF) (hG := hG) := by
  intro cfg id s
  wp_start as #Hzlg
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  try ipersist cfg
  try ihave #Hcf := cfg
  try iStructNamedSuffix Hcf "F"
  try wp_auto
  wp_apply (hNamed cfg.Logger' go!"raft") as %l' #Hl'
  · iframe #
  wp_apply (hNRL l') as %lg ⟨%lok, %Hlg, #Hlok⟩
  · iframe #
  subst Hlg
  try wp_auto
  iapply HΦ
  iexists lok
  iframe Hlok
  unfold raftCfgOf
  iframe

end proof

end EtcdGrove
end Perennial
