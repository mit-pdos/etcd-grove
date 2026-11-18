/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBackend__CreateAuthBuckets.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__CreateAuthBuckets
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBackend.CreateAuthBuckets.wp_proof
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG) := by
  intro abe γ P W Pk b qo S r h3
  obtain ⟨ha1, ha2, ha3⟩ := h3 mvcc.authBI (by simp)
  obtain ⟨hu1, hu2, hu3⟩ := h3 mvcc.authUsersBI (by simp)
  obtain ⟨hr1, hr2, hr3⟩ := h3 mvcc.authRolesBI (by simp)
  wp_start as ⟨#Hbe, #HB, Ho, Hwb, Hrb⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HA0, -⟩, ⟨%ub, #HU0, -⟩, ⟨%rb, #HR0, -⟩, -⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hba := schema.auth_isBucket hID hName hSafe ab $$ [$Hpkg $HA0]
  ihave #Hbu := schema.authUsers_isBucket hID hName hSafe ub $$ [$Hpkg $HU0]
  ihave #Hbr := schema.authRoles_isBucket hID hName hSafe rb $$ [$Hpkg $HR0]
  icases backend.isBackend_b γ P W Pk b $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  -- the three buckets' parts apart from the rest
  have hsplit : ∀ n, S n ↔ (n = mvcc.authBI.name ∨ (n = mvcc.authUsersBI.name ∨
      (n = mvcc.authRolesBI.name ∨ (S n ∧ n ≠ mvcc.authBI.name ∧ n ≠ mvcc.authUsersBI.name ∧
        n ≠ mvcc.authRolesBI.name)))) := by
    intro n
    constructor
    · intro h
      by_cases e1 : n = mvcc.authBI.name
      · exact Or.inl e1
      by_cases e2 : n = mvcc.authUsersBI.name
      · exact Or.inr (Or.inl e2)
      by_cases e3 : n = mvcc.authRolesBI.name
      · exact Or.inr (Or.inr (Or.inl e3))
      exact Or.inr (Or.inr (Or.inr ⟨h, e1, e2, e3⟩))
    · rintro (rfl | rfl | rfl | ⟨h, -⟩)
      · exact ha3
      · exact hu3
      · exact hr3
      · exact h
  have hne12 : mvcc.authBI.name ≠ mvcc.authUsersBI.name := by decide
  have hne13 : mvcc.authBI.name ≠ mvcc.authRolesBI.name := by decide
  have hne23 : mvcc.authUsersBI.name ≠ mvcc.authRolesBI.name := by decide
  ihave Hrb := (rbPart_set γ S _ r hsplit).1 $$ Hrb
  icases (rbPart_split γ (· = mvcc.authBI.name) _ r (by
    rintro n rfl (h | h | ⟨-, h, -⟩)
    · exact hne12 h
    · exact hne13 h
    · exact h rfl)).1 $$ Hrb with ⟨HpA, Hrb⟩
  icases (rbPart_split γ (· = mvcc.authUsersBI.name) _ r (by
    rintro n rfl (h | ⟨-, -, h, -⟩)
    · exact hne23 h
    · exact h rfl)).1 $$ Hrb with ⟨HpU, Hrb⟩
  icases (rbPart_split γ (· = mvcc.authRolesBI.name) _ r (by
    rintro n rfl ⟨-, -, -, h⟩
    exact h rfl)).1 $$ Hrb with ⟨HpR, HpO⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hBT γ P W Pk b) $$ [$Hbpkg $HB] as %t #Ht
  (try wp_auto)
  wp_apply (hLO γ P W Pk b t qo) $$ [$Hbpkg $HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  have hlim := HPw.2.2.1
  have hhm := HPw.2.2.2.1
  have hp0 := Hfree.2.1
  have hz1 : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  have hz2 : sint.Z (st.pend + W64 1 + W64 1) = sint.Z st.pend + 2 := by word
  have hz3 : sint.Z (st.pend + W64 1 + W64 1 + W64 1) = sint.Z st.pend + 3 := by word
  wp_apply (schema.wp_create_tracked hCB γ P W Pk b t st ab mvcc.authBI r ha1 ha2 (by decide)
      (by decide) (by omega)) $$ [$Hbpkg $HB $Ht $Hl $Hba $HpA] as ⟨Hl, HpA⟩
  (try wp_auto)
  wp_apply (schema.wp_create_tracked hCB γ P W Pk b t (st.create mvcc.authBI) ub mvcc.authUsersBI r
      hu1 hu2 (by decide) (by decide) (by show sint.Z (st.pend + W64 1) + 1 < 2 ^ 58; omega))
    $$ [$Hbpkg $HB $Ht $Hl $Hbu $HpU] as ⟨Hl, HpU⟩
  (try wp_auto)
  wp_apply (schema.wp_create_tracked hCB γ P W Pk b t ((st.create mvcc.authBI).create mvcc.authUsersBI)
      rb mvcc.authRolesBI r hr1 hr2 (by decide) (by decide)
      (by show sint.Z (st.pend + W64 1 + W64 1) + 1 < 2 ^ 58; omega))
    $$ [$Hbpkg $HB $Ht $Hl $Hbr $HpR] as ⟨Hl, HpR⟩
  (try wp_auto)
  -- the parts back together, at the buckets present
  have hcA : ∀ n, n = mvcc.authBI.name → (r.insert mvcc.authBI.name
      ((r.lookup mvcc.authBI.name).getD ∅)).lookup n = (schema.authCreated r).lookup n := by
    rintro n rfl
    unfold schema.authCreated
    rw [GMap.lookup_insert, GMap.lookup_insert_ne _ _ (Ne.symm hne13),
      GMap.lookup_insert_ne _ _ (Ne.symm hne12), GMap.lookup_insert]
  have hcU : ∀ n, n = mvcc.authUsersBI.name → (r.insert mvcc.authUsersBI.name
      ((r.lookup mvcc.authUsersBI.name).getD ∅)).lookup n = (schema.authCreated r).lookup n := by
    rintro n rfl
    unfold schema.authCreated
    rw [GMap.lookup_insert, GMap.lookup_insert_ne _ _ (Ne.symm hne23), GMap.lookup_insert]
  have hcR : ∀ n, n = mvcc.authRolesBI.name → (r.insert mvcc.authRolesBI.name
      ((r.lookup mvcc.authRolesBI.name).getD ∅)).lookup n = (schema.authCreated r).lookup n := by
    rintro n rfl
    unfold schema.authCreated
    rw [GMap.lookup_insert, GMap.lookup_insert]
  have hcO : ∀ n, (S n ∧ n ≠ mvcc.authBI.name ∧ n ≠ mvcc.authUsersBI.name ∧
      n ≠ mvcc.authRolesBI.name) → r.lookup n = (schema.authCreated r).lookup n := by
    rintro n ⟨-, h1, h2, h3⟩
    unfold schema.authCreated
    rw [GMap.lookup_insert_ne _ _ (Ne.symm h3), GMap.lookup_insert_ne _ _ (Ne.symm h2),
      GMap.lookup_insert_ne _ _ (Ne.symm h1)]
  ihave HpA : rbPart γ (· = mvcc.authBI.name) (schema.authCreated r) $$ [HpA]
  · iapply (rbPart_congr γ _ _ _ hcA).1
    iExactEq HpA; rfl
  ihave HpU : rbPart γ (· = mvcc.authUsersBI.name) (schema.authCreated r) $$ [HpU]
  · iapply (rbPart_congr γ _ _ _ hcU).1
    iExactEq HpU; rfl
  ihave HpR : rbPart γ (· = mvcc.authRolesBI.name) (schema.authCreated r) $$ [HpR]
  · iapply (rbPart_congr γ _ _ _ hcR).1
    iExactEq HpR; rfl
  ihave HpO := (rbPart_congr γ _ _ _ hcO).1 $$ HpO
  ihave Hrb := (rbPart_split γ (· = mvcc.authRolesBI.name) _ (schema.authCreated r) (by
    rintro n rfl ⟨-, -, -, h⟩
    exact h rfl)).2 $$ [$HpR $HpO]
  ihave Hrb := (rbPart_split γ (· = mvcc.authUsersBI.name) _ (schema.authCreated r) (by
    rintro n rfl (h | ⟨-, -, h, -⟩)
    · exact hne23 h
    · exact h rfl)).2 $$ [$HpU $Hrb]
  ihave Hrb := (rbPart_split γ (· = mvcc.authBI.name) _ (schema.authCreated r) (by
    rintro n rfl (h | h | ⟨-, h, -⟩)
    · exact hne12 h
    · exact hne13 h
    · exact h rfl)).2 $$ [$HpA $Hrb]
  ihave Hrb := (rbPart_set γ S _ (schema.authCreated r) hsplit).2 $$ Hrb
  -- the deferred `tx.Unlock()`: nothing the readers see changed; the part idle
  have hvs := mvcc.viewSame_create mvcc.authRolesBI (mvcc.viewSame_create mvcc.authUsersBI
    (mvcc.viewSame_create mvcc.authBI (backend.viewSame_of_freeOk Hfree)))
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin γ P _ hvs
  wp_apply (hUL γ P W Pk b t (((st.create mvcc.authBI).create mvcc.authUsersBI).create
      mvcc.authRolesBI) iprop(True) S (schema.authCreated r) Hfree.2.2.2.2
      (by show sint.Z (st.pend + W64 1 + W64 1 + W64 1) + P.hookMax < 2 ^ 58; omega))
    $$ [$Hbpkg $HB $Ht $Hl $Hwb $Hrb HW HPk] as ⟨-, Hrb⟩
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
