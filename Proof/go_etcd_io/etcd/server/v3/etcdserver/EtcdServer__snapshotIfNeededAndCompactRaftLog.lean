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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDSnapLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.wp_proof
    (hD : EtcdServer.shouldSnapshotToDisk.spec (GF := GF) (hG := hG))
    (hM : EtcdServer.shouldSnapshotToMemory.spec (GF := GF) (hG := hG))
    (hS : EtcdServer.snapshot.spec (GF := GF) (hG := hG))
    (hC : EtcdServer.compactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs nid γp w TM ρ kv RC RC' sa hok haw hci hrel
  wp_start as ⟨#Hsrv, #Hsd, #Hal, #Hkv, Hcok, HRC, #Hss, #Hsa, #HWP, #HWA, HSS, #Hapl, Hai, Hat,
    Hcs, Hst, Hbe, Happ, Hlr, HKV⟩
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, -, -, -, -, #Hsc, -, ⟨%scu, #Hscu, -⟩, #Hinf,
    ⟨%lg, #Hlgf, %Hlgn⟩⟩
  ihave #Hss' := Hss
  iunfold srvSnapStor at Hss'
  icases Hss' with ⟨#Hmsi, -⟩
  iunfold srvSnapState at HSS
  icases HSS with ⟨%d, %m, %f, Hd, Hm, Hf, %Hdm, #Hms, #Hslb, #Hfa, #Hfb⟩
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
    isplitl [HRC]
    · ileft; iexact HRC
    isplitl [Hd Hm Hf]
    · iunfold srvSnapState; iexists d, m, f; iframe Hd Hm Hf Hms Hfa Hfb
      isplitr
      · ipureintro; exact Hdm
      iapply memSnapLb_mono γs _ _ (by simp) $$ Hslb
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
    -- (E3p) `snapshot` takes the row's part shared by both auth modes
    icases srvApplyKVM_core E.authOn s E γw x sa $$ HKV with ⟨%ua, HKV, HKVk⟩
    first
      | (wp_apply hS s γ ci TM E ρ γr γw b ep st ai at' cs a t x true ms γs nid (W64 0) kv RC RC' ua
            hok hci hrel $$ [Hd Hm Hf Hai Hat Hcs Hst Hbe Happ Hlr HKV HRC Hcok]
          as ⟨%st', HSS, HRC, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %hst'⟩
         · iframe #
           iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV Hcok
           simp only [↓reduceIte]
           iframe HRC
           iunfold srvSnapState; iexists d, m, f; iframe Hd Hm Hf Hms Hslb Hfa Hfb
           ipureintro; exact Hdm
         simp only [↓reduceIte] at *
         ihave HRC : iprop(RC ∨ RC') $$ [HRC]
         · iright; iexact HRC)
      | (wp_apply hS s γ ci TM E ρ γr γw b ep st ai at' cs a t x false ms γs nid (W64 0) kv RC RC' ua
            hok hci hrel $$ [Hd Hm Hf Hai Hat Hcs Hst Hbe Happ Hlr HKV Hcok]
          as ⟨%st', HSS, -, Hai, Hat, Hcs, Hst, Hbe, Happ, Hlr, HKV, %hst'⟩
         · iframe #
           iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV Hcok
           simp only [Bool.false_eq_true, ↓reduceIte]
           isplitl [Hd Hm Hf]
           · iunfold srvSnapState; iexists d, m, f; iframe Hd Hm Hf Hms Hslb Hfa Hfb
             ipureintro; exact Hdm
           itrivial
         ihave HRC : iprop(RC ∨ RC') $$ [HRC]
         · ileft; iexact HRC)
    iunfold srvSnapState at HSS
    icases HSS with ⟨%d', %m', %f', Hd, Hm, Hf, %Hdm', -, #Hslb', #Hfa', #Hfb'⟩
    (try wp_auto)
    have hcI : 1 ≤ compactIdx ai scu ∧ compactIdx ai scu ≤ uint.nat ai := by
      unfold compactIdx; split <;> constructor <;> word
    ihave #Hfr := srvFrozen_get γs (uint.nat ai) (compactIdx ai scu) hcI.1 hcI.2 $$ [$Hfa' $Hfb']
    wp_apply hC s ai ms γs γr.raft.raft nid scu lg Hai1 $$ [Hlr] as Hlr
    · iframe #; iframe Hlr; ipureintro; exact Hlgn
    (try wp_auto)
    ihave HKV := HKVk $$ HKV
    iapply HΦ
    iexists st'
    iframe Hai Hat Hcs Hst Hbe Happ Hlr HKV HRC
    isplitl [Hd Hm Hf]
    · iunfold srvSnapState; iexists d', m', f'; iframe Hd Hm Hf Hms Hfa' Hfb'
      isplitr
      · ipureintro; exact Hdm'
      iapply memSnapLb_mono γs _ _ (by simp) $$ Hslb'
    ipureintro; exact hst')

end proof

end EtcdGrove
end Perennial
