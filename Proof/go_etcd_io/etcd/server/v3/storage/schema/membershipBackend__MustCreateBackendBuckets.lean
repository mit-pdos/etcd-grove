/-
Proof of `Spec/.../schema/membershipBackend__MustCreateBackendBuckets.lean`: the backend's `BatchTx`,
`LockOutsideApply`, three `UnsafeCreateBucket`s of present buckets, the deferred `Unlock`. Lean-first
(prove-ps2-members, 2026-11-22).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustCreateBackendBuckets
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBkts
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBktsFresh

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.membershipBackend.MustCreateBackendBuckets.wp_proof
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.membershipBackend.MustCreateBackendBuckets.spec (GF := GF) (hG := hG) := by
  intro mbl d W Pk qo S r hS hm hmr hc hrm hrmr hrc
  wp_start as ⟨#Hbe, #HB, Ho, Hwb, Hrb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bm, #HM, -⟩, -, ⟨%bmr, #HMR, -⟩,
    ⟨%bc, #HC, -⟩, -⟩
  ihave #Hbm := schema.members_isBucket hID hName hSafe bm $$ [$Hpkg $HM]
  ihave #Hbmr := schema.membersRemoved_isBucket hID hName hSafe bmr $$ [$Hpkg $HMR]
  ihave #Hbc := schema.cluster_isBucket hID hName hSafe bc $$ [$Hpkg $HC]
  icases backend.isBackend_b d.γB d.P W Pk d.be $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  have hRB : ∀ n, membership.clusterBkts n → d.P.RB n = true := by
    intro n h
    simp only [membership.clusterBkts, membership.memberBkts] at h
    rcases h with (rfl | rfl) | rfl <;> simp [mvcc.KBReal.P, mvcc.restBuckets]
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hbpkg $HB] as %t #Ht
  (try wp_auto)
  wp_apply (hLO d.γB d.P W Pk d.be t qo) $$ [$Hbpkg $HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  have hlim := HPw.2.2.1
  have hp0 := Hfree.2.1
  wp_apply (schema.create_present hCB d.γB d.P W Pk d.be t st bm mvcc.membersBI S r
      (hS _ (Or.inl (Or.inl rfl))) (hRB _ (Or.inl (Or.inl rfl))) hm (by decide) (by decide)
      (by omega) hrm) $$ [$Hbpkg $HB $Ht $Hl $Hbm $Hrb] as ⟨Hl, Hrb, %Hs1⟩
  (try wp_auto)
  have hp1 : sint.Z (st.create mvcc.membersBI).pend = sint.Z st.pend + 1 := by
    show sint.Z (st.pend + W64 1) = _; word
  wp_apply (schema.create_present hCB d.γB d.P W Pk d.be t _ bmr mvcc.membersRemovedBI S r
      (hS _ (Or.inl (Or.inr rfl))) (hRB _ (Or.inl (Or.inr rfl))) hmr (by decide) (by decide)
      (by omega) hrmr) $$ [$Hbpkg $HB $Ht $Hl $Hbmr $Hrb] as ⟨Hl, Hrb, %Hs2⟩
  (try wp_auto)
  have hp2 : sint.Z ((st.create mvcc.membersBI).create mvcc.membersRemovedBI).pend =
      sint.Z st.pend + 2 := by
    show sint.Z (st.pend + W64 1 + W64 1) = _; word
  wp_apply (schema.create_present hCB d.γB d.P W Pk d.be t _ bc mvcc.clusterBI S r
      (hS _ (Or.inr rfl)) (hRB _ (Or.inr rfl)) hc (by decide) (by decide)
      (by omega) hrc) $$ [$Hbpkg $HB $Ht $Hl $Hbc $Hrb] as ⟨Hl, Hrb, %Hs3⟩
  (try wp_auto)
  -- the deferred `Unlock()`: nothing the readers see changed; the part idle
  have hvs := mvcc.viewSame_create mvcc.clusterBI (mvcc.viewSame_create mvcc.membersRemovedBI
    (mvcc.viewSame_create mvcc.membersBI (backend.viewSame_of_freeOk Hfree)))
  have hroom : sint.Z (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create
      mvcc.clusterBI).pend + d.P.hookMax < 2 ^ 58 := by
    have h2 := HPw.2.2.2.1
    have : sint.Z (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create
        mvcc.clusterBI).pend = sint.Z st.pend + 3 := by
      show sint.Z (st.pend + W64 1 + W64 1 + W64 1) = _; word
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin d.γB d.P _ hvs
  wp_apply (backend.batchTxBuffered.Unlock.spec_free hUL d.γB d.P W Pk d.be t
      (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create mvcc.clusterBI) iprop(True) S r
      Hfree.2.2.2.2.1 hroom) $$ [$Hbpkg $HB $Ht $Hl $Hwb $Hrb HW HPk] as ⟨-, Hrb⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb

theorem schema.membershipBackend.MustCreateBackendBuckets.wp_proofFresh
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.membershipBackend.MustCreateBackendBuckets.specFresh (GF := GF) (hG := hG) := by
  intro mbl d W Pk qo S r hS hm hmr hc
  wp_start as ⟨#Hbe, #HB, Ho, Hwb, Hrb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%bm, #HM, -⟩, -, ⟨%bmr, #HMR, -⟩,
    ⟨%bc, #HC, -⟩, -⟩
  ihave #Hbm := schema.members_isBucket hID hName hSafe bm $$ [$Hpkg $HM]
  ihave #Hbmr := schema.membersRemoved_isBucket hID hName hSafe bmr $$ [$Hpkg $HMR]
  ihave #Hbc := schema.cluster_isBucket hID hName hSafe bc $$ [$Hpkg $HC]
  icases backend.isBackend_b d.γB d.P W Pk d.be $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  have hRB : ∀ n, membership.clusterBkts n → d.P.RB n = true := by
    intro n h
    simp only [membership.clusterBkts, membership.memberBkts] at h
    rcases h with (rfl | rfl) | rfl <;> simp [mvcc.KBReal.P, mvcc.restBuckets]
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hbpkg $HB] as %t #Ht
  (try wp_auto)
  wp_apply (hLO d.γB d.P W Pk d.be t qo) $$ [$Hbpkg $HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  have hlim := HPw.2.2.1
  have hp0 := Hfree.2.1
  wp_apply (schema.create_any hCB d.γB d.P W Pk d.be t st bm mvcc.membersBI S r
      (hS _ (Or.inl (Or.inl rfl))) (hRB _ (Or.inl (Or.inl rfl))) hm (by decide) (by decide)
      (by omega)) $$ [$Hbpkg $HB $Ht $Hl $Hbm $Hrb] as ⟨Hl, Hrb⟩
  (try wp_auto)
  have hp1 : sint.Z (st.create mvcc.membersBI).pend = sint.Z st.pend + 1 := by
    show sint.Z (st.pend + W64 1) = _; word
  wp_apply (schema.create_any hCB d.γB d.P W Pk d.be t _ bmr mvcc.membersRemovedBI S _
      (hS _ (Or.inl (Or.inr rfl))) (hRB _ (Or.inl (Or.inr rfl))) hmr (by decide) (by decide)
      (by omega)) $$ [$Hbpkg $HB $Ht $Hl $Hbmr $Hrb] as ⟨Hl, Hrb⟩
  (try wp_auto)
  have hp2 : sint.Z ((st.create mvcc.membersBI).create mvcc.membersRemovedBI).pend =
      sint.Z st.pend + 2 := by
    show sint.Z (st.pend + W64 1 + W64 1) = _; word
  wp_apply (schema.create_any hCB d.γB d.P W Pk d.be t _ bc mvcc.clusterBI S _
      (hS _ (Or.inr rfl)) (hRB _ (Or.inr rfl)) hc (by decide) (by decide)
      (by omega)) $$ [$Hbpkg $HB $Ht $Hl $Hbc $Hrb] as ⟨Hl, Hrb⟩
  ihave Hrb : backend.rbPart d.γB S (schema.withMemBkts r) $$ [Hrb]
  · iapply (backend.rbPart_congr d.γB S _ _ (fun n _ => ?_)).1 $$ Hrb
    rw [schema.withMemBkts_lookup]
    show (((r.insert go!"members" (backend.bktOf r go!"members")).insert go!"members_removed"
      (backend.bktOf (r.insert go!"members" (backend.bktOf r go!"members")) go!"members_removed")).insert go!"cluster"
      (backend.bktOf ((r.insert go!"members" (backend.bktOf r go!"members")).insert go!"members_removed"
        (backend.bktOf (r.insert go!"members" (backend.bktOf r go!"members")) go!"members_removed")) go!"cluster")).lookup n = _
    unfold backend.bktOf
    simp only [GMap.lookup_insert_eq_iff]
    by_cases h1 : go!"cluster" = n
    · subst h1; simp
    by_cases h2 : go!"members_removed" = n
    · subst h2; simp
    by_cases h3 : go!"members" = n
    · subst h3; simp
    have h : ¬ (n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members") := by
      rintro (h | h | h) <;> simp_all
    simp only [h1, h2, h3, h, ite_false]
  (try wp_auto)
  -- the deferred `Unlock()`: nothing the readers see changed; the part idle
  have hvs := mvcc.viewSame_create mvcc.clusterBI (mvcc.viewSame_create mvcc.membersRemovedBI
    (mvcc.viewSame_create mvcc.membersBI (backend.viewSame_of_freeOk Hfree)))
  have hroom : sint.Z (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create
      mvcc.clusterBI).pend + d.P.hookMax < 2 ^ 58 := by
    have h2 := HPw.2.2.2.1
    have : sint.Z (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create
        mvcc.clusterBI).pend = sint.Z st.pend + 3 := by
      show sint.Z (st.pend + W64 1 + W64 1 + W64 1) = _; word
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin d.γB d.P _ hvs
  wp_apply (backend.batchTxBuffered.Unlock.spec_free hUL d.γB d.P W Pk d.be t
      (((st.create mvcc.membersBI).create mvcc.membersRemovedBI).create mvcc.clusterBI) iprop(True) S (schema.withMemBkts r)
      Hfree.2.2.2.2.1 hroom) $$ [$Hbpkg $HB $Ht $Hl $Hwb $Hrb HW HPk] as ⟨-, Hrb⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb

end proof

end EtcdGrove
end Perennial
