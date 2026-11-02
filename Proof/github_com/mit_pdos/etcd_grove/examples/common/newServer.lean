/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/newServer.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

Since 2026-11-02 (periodic mode) `newServer` is `newServerMode` in revision mode: both specs are
`newServerMode.spec`'s at its compaction modes (off, on in revision mode); the configuration's steps
are `newServerMode.wp_proof`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.newServerMode

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

/-- `newServer` with the auto-compactor off: `newServerMode` in revision mode at retention `0`. -/
theorem newServer.wp_proof
    (wp_newServerMode : newServerMode.spec (GF := GF) (hG := hG)) :
    newServer.spec (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ
    ρ E₀ Φs γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hret Hck Haf Hbuq
    Hdbo
  wp_start as ⟨#Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn false Htb Hrb48 HrbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg (by simpa using Hret) Hck Haf Hbuq Hdbo)
    $$ [Hmb] as %s %err Hres
  · iframe; iframe #
    iExactEq Hboot; simp
  (try wp_auto)
  iapply HΦ
  iexact Hres

/-- `newServer` with the auto-compactor on (M2's S4, `notes/m2-plan.md`): `newServerMode` in revision
mode at a positive retention. -/
theorem newServer.wp_proofCompact
    (wp_newServerMode : newServerMode.spec (GF := GF) (hG := hG)) :
    newServer.specCompact (GF := GF) (hG := hG) := by
  intro CS N name peerAddr client token retention snapCount catchUp peer cluster lg M iu Uok ps bootLog ctxs dir id γ
    ρ E₀ Φs γn Htb Hrb48 HrbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg Hret Hcret Hck Haf Hbuq
    Hdbo
  wp_start as ⟨#Hpeer, #Hcl, #Hsls, #Hboot, #Hcom, #Hcci, Hmb, #Hnet⟩
  (try wp_auto)
  wp_apply (wp_newServerMode N name peerAddr client token go!"revision" retention snapCount catchUp
      peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ E₀ Φs γn true Htb Hrb48 HrbN hvs hrule
      hboot hblen Hγn1 Hγn2 Hdirok Hdir HU Hlg (by simp only [↓reduceIte]; exact Or.inl ⟨trivial, Hret, Hcret⟩) Hck Haf Hbuq Hdbo)
    $$ [Hmb] as %s %err Hres
  · iframe; iframe #
    iExactEq Hboot; simp
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end common
end EtcdGrove
end Perennial
