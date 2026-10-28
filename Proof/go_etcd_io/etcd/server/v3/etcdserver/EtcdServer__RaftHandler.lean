/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__RaftHandler.lean`. Lean-first (no
Rocq counterpart); rafthttp stage 6d (2026-10-24; until then an axiom, D21 stage M5).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Handler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.RaftHandler.wp_proof
    (wp_Handler : rafthttp.Transport.Handler.spec (GF := GF) (hG := hG)) :
    EtcdServer.RaftHandler.spec (GF := GF) (hG := hG) := by
  intro s γn id τ a Hown
  wp_start as #Hm
  iunfold srvNetMember at Hm
  icases Hm with ⟨-, #Htr, %Hlid, #Hst, #Hop, %Hcov⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Handler γn τ.t τ.c a (by rw [Hlid]; exact Hown) (by rw [Hlid]; exact Hcov))
    $$ [] as %h Hh
  · iframe #
  iapply HΦ
  iunfold srvServeRes
  iexact Hh

end proof

end EtcdGrove
end Perennial
