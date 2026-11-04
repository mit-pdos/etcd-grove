/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/stop.lean` (the restart plan's R2a,
2026-11-02): `m.s.HardStop()`, then `m.pl.Close()`, over the drafted `HardStop.spec` and the draft
boundary `http.ListenerClose_spec`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AppliedIndex
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem stop.wp_proof
    (wp_AppliedIndex : EtcdServer.AppliedIndex.spec (GF := GF) (hG := hG))
    (wp_HardStop : EtcdServer.HardStop.spec (GF := GF) (hG := hG))
    (hClose : http.ListenerClose_spec (GF := GF) (hG := hG)) :
    stop.spec (GF := GF) (hG := hG) := by
  intro m s pl γ id peerAddr γn ρ dd
  wp_start as ⟨Hm, %Hb3⟩
  iunfold memberStop at Hm
  icases Hm with ⟨Hrec, Hsr, %Hli, Hcl, %Hγρ, #Hai⟩
  icases Hai with ⟨%E, #Hai⟩
  obtain ⟨li, rfl⟩ := Hli
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  -- the wait: `for m.s.AppliedIndex() < NBoot { time.Sleep(time.Millisecond) }`; on exit the
  -- member applied the bootstrap log
  wp_for Hrec
  wp_apply (wp_AppliedIndex s E ρ.rd) as %v #Hv
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · wp_apply time.wp_Sleep
    (try wp_auto)
    wp_for_post
    iframe
  have Hnlt : ¬ uint.Z v < uint.Z (W64 3) := by
    intro h; apply Hif; congr 1; simp only [decide_eq_true_eq]; word
  rw [if_neg (by simpa using Hnlt)]
  wp_auto
  dsimp only
  have Hba : ρ.rd.raft.raft.boot.length ≤ uint.nat v := by
    rw [Hγρ]; word
  -- `m.s.HardStop()`
  wp_apply (wp_HardStop s γ ρ id dd) $$ [Hsr] as Himg
  · iframe
    iunfold srvBootApplied
    iexists v
    iframe #
    ipureintro; exact Hba
  -- `m.pl.Close()`
  wp_apply (hClose _ li peerAddr (raftProto (netRh γn)) rfl) $$ [Hcl] as %err ⟨Haddr, Hown⟩
  · iexact Hcl
  iapply HΦ
  iframe

end proof

end etcd_restart
end EtcdGrove
end Perennial
