/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/stop.lean` (restart3 C2, 2026-11-15, restart1's (restart S7.5, step e,
2026-11-14): the `AppliedIndex()` wait, then `s.HardStop()` (`HardStop.spec`); restart3's `stop.wp_proof`
without the listener close. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AppliedIndex
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem stop.wp_proof
    (wp_AppliedIndex : EtcdServer.AppliedIndex.spec (GF := GF) (hG := hG))
    (wp_HardStop : EtcdServer.HardStop.spec (GF := GF) (hG := hG)) :
    stop.spec (GF := GF) (hG := hG) := by
  intro s E Ea ρ id dd γn name k Hb1 Hsc
  wp_start as ⟨#Hai, #Hdd, Hsr, Hrds⟩
  icases srvStopRight_dd s E _ ρ id dd _ $$ [$Hsr $Hdd] with ⟨%Hdd', Hsr⟩
  subst Hdd'
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  -- the wait: `for s.AppliedIndex() < k { time.Sleep(time.Millisecond) }`
  wp_for s
  wp_apply (wp_AppliedIndex false s Ea ρ.rd) as %v #Hv
  · rw [srvAppliedInvM_false]; iframe #
  (try wp_auto)
  wp_if_destruct
  · wp_apply time.wp_Sleep
    (try wp_auto)
    wp_for_post
    iframe
  have Hnlt : ¬ uint.Z v < uint.Z k := by
    intro h; apply Hif; congr 1; simp only [decide_eq_true_eq]; word
  (try rw [if_neg (by simpa using Hnlt)])
  wp_auto
  have Hba : ρ.rd.raft.raft.boot.length ≤ uint.nat v := by
    word
  -- `s.HardStop()`
  wp_apply (wp_HardStop s E ρ.rd.raft.raft ρ id (memberDataDir name)) $$ [Hsr Hrds] as Himg
  · iframe Hsr
    iapply srvStopReq_intro s E ρ (memberDataDir name) Hsc
    isplitr
    · iapply srvBootApplied_of_applied ρ v Hba $$ Hv
    isplitr
    · iexact Hdd
    iexact Hrds
  iapply HΦ
  iapply etcdstart.memberRestartRes_intro0
  iexact Himg

end proof

end etcd_restartN
end EtcdGrove
end Perennial
