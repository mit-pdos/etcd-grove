/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/stop.lean` (the restart plan's R2a,
2026-11-02): `m.s.HardStop()`, then `m.pl.Close()`, over the drafted `HardStop.spec` and the draft
boundary `http.ListenerClose_spec`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__HardStop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

theorem stop.wp_proof
    (wp_HardStop : EtcdServer.HardStop.spec (GF := GF) (hG := hG))
    (hClose : http.ListenerClose_spec (GF := GF) (hG := hG)) :
    stop.spec (GF := GF) (hG := hG) := by
  intro m s pl γ id peerAddr γn
  wp_start as ⟨Hm, #Hreq⟩
  iunfold memberStop at Hm
  icases Hm with ⟨Hrec, Hsr, %Hli, Hcl⟩
  obtain ⟨li, rfl⟩ := Hli
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  wp_auto
  -- `m.s.HardStop()`
  wp_apply (wp_HardStop s γ id) $$ [Hsr] as Himg
  · iframe; iframe #
  -- `m.pl.Close()`
  wp_apply (hClose _ li peerAddr (raftProto (netRh γn)) rfl) $$ [Hcl] as %err ⟨Haddr, Hown⟩
  · iexact Hcl
  iapply HΦ
  iframe

end proof

end restart3
end EtcdGrove
end Perennial
