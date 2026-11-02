/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/BuildServer.lean` (2026-11-02, the
restart plan's R2a): `newServer(name, peer, client, cluster, token, 0, snapCount, catchUp, lg)`, its
result returned. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.BuildServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem BuildServer.wp_proof
    (wp_newServer : newServer.spec (GF := GF) (hG := hG)) :
    BuildServer.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs
    dir id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hck Haf
    Hbuq Hdbo
  wp_start as ⟨#Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
  (try wp_auto)
  -- `newServer(name, peer, client, cluster, token, 0, snapCount, catchUp, lg)`: the compactor off
  wp_apply (wp_newServer N name peerAddr client token (W64 0) snapCount catchUp peer cluster lg M iu
      Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok
      Hdir HU Hlg (by decide) Hck Haf Hbuq Hdbo) $$ [Hmb] as %s %err Hres
  · iframe; iframe #
  iapply HΦ
  iexact Hres

end proof

end common
end EtcdGrove
end Perennial
