/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__snapshotIfNeededAndCompactRaftLog.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__shouldSnapshotToDisk
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__shouldSnapshotToMemory
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__compactRaftLog

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.wp_proof
    (hD : EtcdServer.shouldSnapshotToDisk.spec (GF := GF) (hG := hG))
    (hM : EtcdServer.shouldSnapshotToMemory.spec (GF := GF) (hG := hG))
    (hS : EtcdServer.snapshot.spec (GF := GF) (hG := hG))
    (hC : EtcdServer.compactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG) := by
  intro s E γ ci b γr ep st ai at' cs a t x hok
  wp_start as ⟨#Hsa, Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV⟩
  iunfold isServerApplyAll at Hsa
  icases Hsa with ⟨%wt, %msc, %sc, -, -, -, -, #Hsc⟩
  iunfold srvSnapState at Hss
  icases Hss with ⟨%d, %m, %f, Hd, Hm, Hf⟩
  (try wp_auto)
  wp_apply hD s ep f ai d sc $$ [Hf Hai Hd] as %r1 ⟨Hf, Hai, Hd⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply hM s ep ai m $$ [Hai Hm] as %r2 ⟨Hai, Hm⟩
  · iframe #; iframe
  (try wp_auto)
  cases r1 <;> cases r2
  · -- nothing due: return
    (try wp_auto)
    iapply HΦ
    iexists st
    iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV
    isplitl [Hd Hm Hf]
    · iunfold srvSnapState; iexists d, m, f; iframe
    ipureintro; exact ⟨hok, rfl⟩
  all_goals (
    (try wp_auto)
    wp_apply hS s E γ ci b ep st ai at' cs a t x _ hok $$ [Hd Hm Hf Hai Hat Hcs Hst Hbe Happ Hlr HKV]
      as ⟨%st', Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %hst'⟩
    · iframe #
      iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV
      iunfold srvSnapState; iexists d, m, f; iframe
    (try wp_auto)
    wp_apply hC s ai $$ [Hlr] as Hlr
    · iframe #; iframe Hlr
    (try wp_auto)
    iapply HΦ
    iexists st'
    iframe
    ipureintro; exact hst')

end proof

end EtcdGrove
end Perennial
