/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/Main.lean` (lease-mono3
step 1, 2026-11-06, `notes/lease-mono3-plan.md`): `zap.NewNop()`, then `run` at its logger.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_run : run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id₁ id₂ id₃ ps ctxs boot
  wp_start as ⟨Hstart, Htok, #Hprem, %Hbf, %Hp₂, %Hp₃, %Hp₄, %Hp₅⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Plc : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  wp_apply (wp_run N id₁ id₂ id₃ ps ctxs boot lg) $$ [Hstart Htok] as %r -
  · iframe; iframe #
    ipureintro; exact ⟨⟨Hbf, Hlg⟩, Hp₂, Hp₃, Hp₄, Hp₅⟩
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end etcd_leasecatchup
end EtcdGrove
end Perennial
