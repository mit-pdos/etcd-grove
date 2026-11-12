/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/peer__Resume.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__Resume
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.peer.Resume.wp_proof
    (hReader : rafthttp.streamReader.resume.spec (GF := GF) (hG := hG)) :
    rafthttp.peer.Resume.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd R p
  wp_start as #Hp
  iunfold peerOk at Hp
  icases Hp with ⟨%lg, %ps, %pk, %cw2, %cw1, %pl, %ss, %cr2, %cr1, %r, %rc, %pc, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, #Hcr2, #Hsr2, -, #Hcr1, #Hsr1, -, -, -, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (peerLockInv p) $$ [] as ⟨Hlocked, Hinv⟩
  · iexact Hmu
  iunfold peerLockInv at Hinv
  icases Hinv with ⟨%b, Hb⟩
  (try wp_auto)
  wp_apply hReader Rh lid pid γd cr1 $$ []
  · iframe #
  (try wp_auto)
  wp_apply hReader Rh lid pid γd cr2 $$ []
  · iframe #
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hb]
  · iframe Hmu Hlocked
    inext; iunfold peerLockInv; iexists _; iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
