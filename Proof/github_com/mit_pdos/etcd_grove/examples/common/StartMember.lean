/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/StartMember.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

`NewMember`, whose error is returned with the thread token, then `s.Start()` (`wp_Start_built`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Start

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

theorem StartMember.wp_proof
    (wp_NewMember : NewMember.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    StartMember.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs
    γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hck Haf
    Hbuq Hdbo
  wp_start as ⟨Haddr, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hpown⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_NewMember N name peerAddr client token peer cluster lg M iu Uok ps bootLog ctxs dir id
      γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU
      Hlg Hck Haf Hbuq Hdbo) $$ [Haddr Hmb Hpown] as %s %err Hres
  · iframe; iframe #
  icases Hres with (%Herr | ⟨%Herr, Hmb⟩)
  · -- `NewMember` failed: the error returned, with the thread token
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  -- `s.Start()`
  wp_apply (wp_Start_built wp_Start s ρ E₀ lg γn id N _ HrbN) $$ [Hmb Htok] as Hup
  · iframe
  (try wp_auto)
  iapply HΦ
  iright
  iframe
  ipureintro; rfl

end proof

end common
end EtcdGrove
end Perennial
