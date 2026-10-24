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
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs γp hok hcap
  wp_start as ⟨#Hsa, #HWP, #HWA, Hss, #Hfl, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV⟩
  iunfold isServerApplyAll at Hsa
  icases Hsa with ⟨%wt, %msc, %sc, -, -, -, -, #Hsc, -, ⟨%scu, #Hscu, %Hrbs⟩, #Hinf⟩
  -- (D21 M3) the applied index below the receipts' bound, so at most `SnapshotCatchUpEntries`
  imod srvWTPool_bound E γp ai $$ HWP HWA with %Hrb
  have Hcmp : (if uint.Z scu < uint.Z ai then uint.Z ai - uint.Z scu else 1) ≤ γs.cap := by
    split <;> omega
  iunfold srvSnapState at Hss
  icases Hss with ⟨%d, %m, %f, Hd, Hm, Hf, %Hdm, #Hms, %σ, Htok, %Hσ⟩
  (try wp_auto)
  wp_apply hD s ep f ai d sc $$ [Hf Hai Hd] as %r1 ⟨Hf, Hai, Hd, %Hr1⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply hM s ep ai m $$ [Hai Hm] as %r2 ⟨Hai, Hm, %Hr2⟩
  · iframe #; iframe
  (try wp_auto)
  cases r1 <;> cases r2
  · -- nothing due: return
    (try wp_auto)
    iapply HΦ
    iexists st
    iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV
    isplitl [Hd Hm Hf Htok]
    · iunfold srvSnapState; iexists d, m, f; iframe Hd Hm Hf Hms
      isplitr
      · ipureintro; exact Hdm
      iexists σ; iframe Htok; ipureintro; exact ⟨Hσ.1, by word⟩
    ipureintro; exact ⟨hok, rfl⟩
  all_goals (
    -- (D19i part 1) the trigger fires only past index `0`
    have Hai1 : 1 ≤ uint.Z ai := by
      first
        | (have := Hr2 rfl; omega)
        | (have h := Hr1 rfl
           have : uint.Z ai ≠ uint.Z d := fun e => h (by word)
           have := Hdm.1
           have : 0 ≤ uint.Z d := by word
           omega)
    (try wp_auto)
    wp_apply hS s E γw γ ci b ep st ai at' cs a t x _ ms γs (W64 0) hok
        $$ [Hd Hm Hf Htok Hai Hat Hcs Hst Hbe Happ Hlr HKV]
      as ⟨%st', Hss, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %hst'⟩
    · iframe #
      iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV
      iunfold srvSnapState; iexists d, m, f; iframe Hd Hm Hf Hms
      isplitr
      · ipureintro; exact Hdm
      iexists σ; iframe Htok; ipureintro; exact ⟨Hσ.1, by word⟩
    iunfold srvSnapState at Hss
    icases Hss with ⟨%d', %m', %f', Hd, Hm, Hf, %Hdm', -, %σ', Htok, %Hσ'⟩
    (try wp_auto)
    wp_apply hC s ai ms γs σ' scu Hσ'.1 Hσ'.2 Hai1 Hcmp $$ [Hlr Htok]
      as ⟨Hlr, %σ'', Htok, %Hσ''⟩
    · iframe #; iframe Hlr Htok
    (try wp_auto)
    iapply HΦ
    iexists st'
    iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV
    isplitl [Hd Hm Hf Htok]
    · iunfold srvSnapState; iexists d', m', f'; iframe Hd Hm Hf Hms
      isplitr
      · ipureintro; exact Hdm'
      iexists σ''; iframe Htok; ipureintro; exact ⟨Hσ''.1, by word⟩
    ipureintro; exact hst')

end proof

end EtcdGrove
end Perennial
