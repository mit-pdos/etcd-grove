/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/serveClient.lean` (the restart
plan's R2a, 2026-11-02): `common.Serve(m.s, client)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.serveClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

theorem serveClient.wp_proof
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG)) :
    serveClient.spec (GF := GF) (hG := hG) := by
  intro CS m s pl addr E ρ γr cfg Q Hlg Htr Hpn Hms Hbuq
  wp_start as ⟨Hm, Haddr, #Hreq, #Hrd, #Hsf, HWR, #Hnrl, Hlgr, Hbemu, Hgo, Hstep⟩
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Serve s addr E ρ γr cfg Q Hlg Htr Hpn Hms Hbuq)
    $$ [Haddr HWR Hlgr Hbemu Hgo Hstep] as %err Hres
  · iframe; iframe #
  iapply HΦ
  iframe

end proof

end restart3
end EtcdGrove
end Perennial
