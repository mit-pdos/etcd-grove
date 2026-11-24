/-
Proofs of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/build.lean` (restart3 C2,
2026-11-15): `etcdstart.BuildServer` at `restart3`'s token and snapshot settings, over
`BuildServer.spec` (`wp_proof`) and `BuildServer.specRestart` (`wp_proofRestart`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.build
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BuildServer

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

theorem build.wp_proof (wp_BuildServer : etcdstart.BuildServer.spec (GF := GF) (hG := hG)) :
    build.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn
    ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf HU8 HnL Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet, Hfresh⟩
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_BuildServer N name peerAddr client token (W64 1) (W64 1) peer cluster lg M iu Uok
      ps bootLog ctxs dir id γ ρ E₀ Φs γn .none HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok
      Hdir Hdirps HU Hpf Hcf HU8 HnL Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh] as %s %err Hres
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  icases Hres with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, Hmb, -, #Hdd⟩)
  · ileft; iframe Htok; ipureintro; exact Herr
  · iright; iframe; iframe #; ipureintro; exact Herr

theorem build.wp_proofRestart (wp_BuildServer : etcdstart.BuildServer.specRestart (GF := GF) (hG := hG)) :
    build.specRestart (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn
    ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, #Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hrr, #Hnet, #Hrfs, #Hvoff⟩
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_BuildServer N name peerAddr client token (W64 1) (W64 1) peer cluster lg M iu Uok
      ps bootLog ctxs dir id γ ρ γn HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok
      Hdir Hdirps HU Hpf Hcf Haf Hbuq Hdbo) $$ [Htok Hrr] as %s %err Hres
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  icases Hres with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, Hb⟩)
  · ileft; iframe Htok; ipureintro; exact Herr
  · iright; iframe; ipureintro; exact Herr

end proof

end etcd_restartN
end EtcdGrove
end Perennial
