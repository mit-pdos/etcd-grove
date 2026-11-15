/- Lean-first (no Rocq counterpart). The proof of `Run`: `runChecks`, then `le.Stop()` with its
stop token and `be.Close()` with the backend's whole open token (`runChecks`' post), whose error
`dbCloseOk` excludes. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem Run.wp_proof
    (wp_runChecks : runChecks.spec (GF := GF) (hG := hG))
    (wp_Stop : lease.lessor.Stop.spec (GF := GF) (hG := hG))
    (wp_Close : backend.backend.Close.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro cfg _ _ hops0 hops hrd0 hrd hw0 hw hdbo hdbc
  wp_start as ⟨Hfile, Htok, #Hvoff⟩
  (try wp_auto)
  wp_apply (wp_runChecks cfg hops0 hops hrd0 hrd hw0 hw hdbo) $$ [Hfile Htok]
    as %rep %lp %b %γB %P %W ⟨Hstop, #Hisb, #Hsc, Hopen⟩
  · iframe Hfile Htok Hvoff
    (try iPkgInit)
  (try wp_auto)
  -- `le.Stop()`
  wp_apply (wp_Stop lp) $$ [Hstop]
  · iframe Hstop; (try iPkgInit)
  (try wp_auto)
  -- `check(be.Close() == nil, …)`
  ihave #Hreq : backend.commitReq (GF := GF) γB P iprop(True) b iprop(True) iprop(True) $$ []
  · iapply backend.commitReq_true
  wp_apply (wp_Close γB P W iprop(True) b iprop(True) iprop(True)) $$ [Hopen]
    as %err ⟨-, %D, -, Hres⟩
  · iframe Hisb Hsc Hopen Hreq
    (try iPkgInit)
  icases Hres with (⟨%Herr, -⟩ | %Hno)
  rotate_left
  · exact absurd hdbc Hno
  subst Herr
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; rfl
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end mvccrand
end EtcdGrove
end Perennial
