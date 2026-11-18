/-
**Schema's auth reader contracts of the real backend** (the authstore-noax stage, 2026-11-18;
`notes/decisions.md`, "authstore-noax"). Lean-first (no Rocq counterpart).

`InvAuthBackend.lean`'s contracts (`schema.authReader r H D`: an `UnsafeReader`'s point reads of the
three auth buckets are the data `D`'s under the token `H`) were stated for schema's auth backend
before anything derived them of the real backend. Here, of the real backend:

* `batch_authReader`: the locked batch transaction (`batchTxBuffered`) at the state `st`, under the
  token `batchLocked γ P b st`, reads the writer's contents (`authDataOf st.S`), by
  `batchTxBuffered.UnsafeRange.spec` (the slices bbolt's, readable under the lock at that
  transaction: its access clause);
* the three buckets of `schema`'s package facts are the backend's `mvcc.authBI`, `authUsersBI`,
  `authRolesBI` (`auth_isBucket`, as `mvcc.lease_isBucket`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ClientLaws
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

/-- **The auth buckets of bbolt's data `S`** (each `∅` if absent). -/
def authDataOf (S : Data) : AuthData :=
  ⟨bktOf S go_etcd_io.etcd.server.v3.storage.schema.authName,
    bktOf S go_etcd_io.etcd.server.v3.storage.schema.authUsersName,
    bktOf S go_etcd_io.etcd.server.v3.storage.schema.authRolesName⟩

section buckets
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- schema's `Auth` bucket is the `Bucket` `mvcc.authBI`. -/
theorem auth_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Auth ↦□ b ⊢ isBucket b mvcc.authBI := by
  unfold mvcc.authBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `AuthUsers` bucket is the `Bucket` `mvcc.authUsersBI`. -/
theorem authUsers_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ b ⊢
      isBucket b mvcc.authUsersBI := by
  unfold mvcc.authUsersBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `AuthRoles` bucket is the `Bucket` `mvcc.authRolesBI`. -/
theorem authRoles_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthRoles ↦□ b ⊢
      isBucket b mvcc.authRolesBI := by
  unfold mvcc.authRolesBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

end buckets

section batch
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **A point read of the locked batch transaction** of the bucket `bi` (the bucket the global `bv`
holds): the writer's contents' entry under the lock's token. -/
theorem batch_authPoint (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (bv : GoString)
    (bi : BucketInfo) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗
      (□ ∀ b0 : GoInterface, globalAddr bv ↦□ b0 -∗ isBucket b0 bi) ⊢
      authPointSpec ⟨go.GoType.PointerType batchTxBuffered.ty, #t⟩ bv (batchLocked γ P b st)
        (bktOf st.S bi.name) := by
  iintro ⟨#Hpkgb, #HB, #Ht, #Hbk⟩
  iunfold authPointSpec
  iintro %b0 %key %kb %dq %Φ !> ⟨#Hg, Hl, Hk⟩ HΦ
  ihave #Hb0 := Hbk $$ %b0 Hg
  ihave Hnil : (slice.nil ↦*{DFrac.discard} ([] : GoString)) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b t st b0 bi key slice.nil kb [] dq DFrac.discard (W64 0)
      (by simp)) $$ [$Hpkgb $HB $Ht $Hl $Hb0 $Hk $Hnil] as %ks %vs ⟨Hl, Hk, -, Hout, #Hacc⟩
  irevert Hout
  rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts]
  iintro Hout
  cases hl : (bktOf st.S bi.name).lookup kb with
  | none =>
    imod kvsOutRd_nil ⊤ st.tx ks vs $$ Hout with ⟨-, #Hvs⟩
    imodintro
    iapply HΦ
    unfold pointValsA
    iframe Hl Hk Hvs
  | some v =>
    imod kvsOutRd_single ⊤ st.tx ks vs kb v $$ Hout with ⟨%ksl, %vsl, -, -, #Hvs, #Hrv⟩
    imodintro
    iapply HΦ
    unfold pointValsA
    iframe Hl Hk
    iexists vsl
    iframe Hvs
    iintro !> Hl
    iapply Hacc $$ %vsl %v %st Hrv Hl
    ipureintro; rfl

/-- **The locked batch transaction reads the writer's auth buckets** (`authReader`, the token
`batchLocked γ P b st`, the data `authDataOf st.S`). -/
theorem batch_authReader (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      authReader ⟨go.GoType.PointerType batchTxBuffered.ty, #t⟩ (batchLocked γ P b st)
        (authDataOf st.S) := by
  iintro ⟨#Hspkg, #Hpkgb, #HB, #Ht⟩
  iunfold authReader
  isplitl []
  · iintro !>
    rw [show (authDataOf st.S).auth = bktOf st.S mvcc.authBI.name from rfl]
    iapply (batch_authPoint hUR γ P W Pk b t st go_etcd_io.etcd.server.v3.storage.schema.Auth mvcc.authBI)
    iframe Hpkgb HB Ht
    iintro !> %b0 #Hg
    iapply auth_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]
  isplitl []
  · iintro !>
    rw [show (authDataOf st.S).users = bktOf st.S mvcc.authUsersBI.name from rfl]
    iapply (batch_authPoint hUR γ P W Pk b t st go_etcd_io.etcd.server.v3.storage.schema.AuthUsers mvcc.authUsersBI)
    iframe Hpkgb HB Ht
    iintro !> %b0 #Hg
    iapply authUsers_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]
  · iintro !>
    rw [show (authDataOf st.S).roles = bktOf st.S mvcc.authRolesBI.name from rfl]
    iapply (batch_authPoint hUR γ P W Pk b t st go_etcd_io.etcd.server.v3.storage.schema.AuthRoles mvcc.authRolesBI)
    iframe Hpkgb HB Ht
    iintro !> %b0 #Hg
    iapply authRoles_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]

end batch

end schema
end EtcdGrove
end Perennial
