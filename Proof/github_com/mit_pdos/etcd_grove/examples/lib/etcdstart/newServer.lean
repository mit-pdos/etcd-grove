/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/newServer.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

Since 2026-11-02 (periodic mode) `newServer` is `newServerMode` in revision mode, at retention `0`;
the configuration's steps are `newServerMode.wp_proof`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.newServerMode

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- `newServer` with the auto-compactor off: `newServerMode` in revision mode at retention `0`. -/
theorem newServer.wp_proof
    (wp_newServerMode : newServerMode.spec (GF := GF) (hG := hG)) :
    newServer.spec (GF := GF) (hG := hG) := by
  intro N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ
    ρ E₀ Φs γn cmp lm Htb Hrb48 HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL Hret Haf Hbuq
    Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn cmp lm Htb Hrb48 HrbN HwbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL (v3compactor.bootCfg_off _ _ _ _ Hret) Haf Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %s %err Hres
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hres

/-- `newServer.wp_proof` with `bootstrap`'s contract borrowing a frame `R` (2026-11-27): `newServerMode.specF`. -/
theorem newServer.wp_proofF
    (wp_newServerMode : newServerMode.specF (GF := GF) (hG := hG)) :
    newServer.specF (GF := GF) (hG := hG) := by
  intro N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ
    ρ E₀ Φs γn cmp lm R Htb Hrb48 HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL Hret Haf Hbuq
    Hdbo
  wp_start as ⟨HR, #Hpkg, #Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn cmp lm R Htb Hrb48 HrbN HwbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL (v3compactor.bootCfg_off _ _ _ _ Hret) Haf Hbuq Hdbo)
    $$ [HR Htok Hmb Hfresh] as %s %err Hres
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hres

/-- `newServer.wp_proof` with the lessor at the caller's name (F7 step 2): `newServerMode.specAt`. -/
theorem newServer.wp_proofAt
    (wp_newServerMode : newServerMode.specAt (GF := GF) (hG := hG)) :
    newServer.specAt (GF := GF) (hG := hG) := by
  intro N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ
    ρ E₀ Φs γn cmp lm γl Htb Hrb48 HrbN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL Hret Haf Hbuq
    Hdbo
  wp_start as ⟨Hlslot, #Hpkg0, #Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn cmp lm γl Htb Hrb48 HrbN HwbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL (v3compactor.bootCfg_off _ _ _ _ Hret) Haf Hbuq Hdbo)
    $$ [Hlslot Htok Hmb Hfresh] as %s %err Hres
  · isplitl [Hlslot]; · iexact Hlslot
    iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hres

/-- `newServer` at a restart: `newServerMode.specRestart` in revision mode. -/
theorem newServer.wp_proofRestart
    (wp_newServerMode : newServerMode.specRestart (GF := GF) (hG := hG)) :
    newServer.specRestart (GF := GF) (hG := hG) := by
  intro N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog
    ctxs dir id γ ρ γn ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf Hret
    Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcci, Hrr, #Hnet, #Hrfs, #Hvoff⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn HwbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf Hret Haf Hbuq Hdbo)
    $$ [Htok Hrr] as %s %err Hres
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end etcdstart
end EtcdGrove
end Perennial
