/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/serveClient.lean` (the restart
plan's R2a, 2026-11-02): `etcdstart.Serve(m.s, client)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.serveClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

theorem serveClient.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG)) :
    serveClient.spec (GF := GF) (hG := hG) := by
  intro CS m s pl addr E ρ γr cfg Q Htr Hpn Hms Hbuq
  wp_start as ⟨#Hzlg, Hm, Haddr, #Hreq, #Hrd, #Hsf, #Hwb, #Hnrl, Hlgr, Hbemu, Hgo, Hstep⟩
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  wp_auto
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off s E ρ γr $$ []
  · iframe #
  wp_apply (wp_Serve s addr E ρ γr cfg Q) $$ [Haddr Hlgr Hbemu Hgo Hstep] as %err Hres
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨Htr, Hpn, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iapply Hstep $$ Hg
  iapply HΦ
  iframe

end proof

end etcd_restart
end EtcdGrove
end Perennial
