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
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeForEach
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

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

section fields
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&atx.<f>` (a `*authBatchTx`). -/
abbrev abtF (f : GoString) (atx : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBatchTx f atx

end fields

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A reader whose users' bucket is empty** (persistent) under the token `H`: its
`UnsafeForEach` over the `AuthUsers` bucket returns `nil` without calling the visitor. -/
def forEachUsersEmpty (r : GoInterfaceOk) (H : IProp GF) : IProp GF :=
  iprop(□ (∀ (bk : GoInterface) (vis : GoFunc),
    {{ H ∗ globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ bk }}
      (App (App (Val #(methods r.ty go!"UnsafeForEach" r.v)) (Val #bk)) (Val #vis))
    {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ H }}))

instance forEachUsersEmpty_persistent (r : GoInterfaceOk) (H : IProp GF) :
    Persistent (forEachUsersEmpty (GF := GF) r H) := by
  unfold forEachUsersEmpty; infer_instance

end defs

/-- **The tracked buckets after `CreateAuthBuckets`**: each auth bucket present (`∅` if it was
absent), the rest as they were. -/
def authCreated (r : GMap GoString BktData) : GMap GoString BktData :=
  ((r.insert mvcc.authBI.name ((r.lookup mvcc.authBI.name).getD ∅)).insert
    mvcc.authUsersBI.name ((r.lookup mvcc.authUsersBI.name).getD ∅)).insert
    mvcc.authRolesBI.name ((r.lookup mvcc.authRolesBI.name).getD ∅)

/-- **The auth buckets of the tracked buckets `r`** (each `∅` if absent). -/
def authDataR (r : GMap GoString BktData) : AuthData :=
  ⟨(r.lookup mvcc.authBI.name).getD ∅, (r.lookup mvcc.authUsersBI.name).getD ∅,
    (r.lookup mvcc.authRolesBI.name).getD ∅⟩

theorem authCreated_auth (r : GMap GoString BktData) :
    (authCreated r).lookup mvcc.authBI.name = some ((r.lookup mvcc.authBI.name).getD ∅) := by
  unfold authCreated
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
    GMap.lookup_insert]

theorem authCreated_users (r : GMap GoString BktData) :
    (authCreated r).lookup mvcc.authUsersBI.name = some ((r.lookup mvcc.authUsersBI.name).getD ∅) := by
  unfold authCreated
  rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert]

theorem authCreated_roles (r : GMap GoString BktData) :
    (authCreated r).lookup mvcc.authRolesBI.name = some ((r.lookup mvcc.authRolesBI.name).getD ∅) := by
  unfold authCreated
  rw [GMap.lookup_insert]

theorem authCreated_other (r : GMap GoString BktData) (n : GoString) (h1 : n ≠ mvcc.authBI.name)
    (h2 : n ≠ mvcc.authUsersBI.name) (h3 : n ≠ mvcc.authRolesBI.name) :
    (authCreated r).lookup n = r.lookup n := by
  unfold authCreated
  rw [GMap.lookup_insert_ne _ _ (Ne.symm h3), GMap.lookup_insert_ne _ _ (Ne.symm h2),
    GMap.lookup_insert_ne _ _ (Ne.symm h1)]

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

/-- **Creating a tracked bucket under the lock** with the bucket's part: the part at the bucket
present (`∅` if it was absent). -/
theorem wp_create_tracked (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (r : GMap GoString BktData) (hhas : P.has bi) (hRB : P.RB bi.name = true)
    (hn0 : 0 < bi.name.length) (hnk : bi.name.length ≤ maxKeySize)
    (hpend : sint.Z st.pend + 1 < 2 ^ 58) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
        rbPart γ (· = bi.name) r }}
      (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
    {{ RET #(); batchLocked γ P b (st.create bi) ∗
        rbPart γ (· = bi.name) (r.insert bi.name ((r.lookup bi.name).getD ∅)) }} := by
  iintro %Φ ⟨#Hpkg, #HB, #Ht, Hl, #Hbk, Hrb⟩ HΦ
  icases batchLocked_rbPart γ P b st (· = bi.name) r $$ [$Hl $Hrb] with ⟨Hl, Hrb, %Hag⟩
  have hrp : rbPut (GF := GF) γ P bi.name st.S = rbPart γ (· = bi.name) (rbData P st.S) := by
    unfold rbPut; rw [hRB]; rfl
  ihave Hrb : rbPut γ P bi.name st.S $$ [Hrb]
  · rw [hrp]
    iapply (rbPart_congr γ _ (rbData P st.S) r (fun n hn => Hag n hn)).2 $$ Hrb
  iapply (hCB γ P W Pk b t st bk bi hhas hn0 hnk hpend) $$ [$Hpkg $HB $Ht $Hl $Hbk $Hrb]
  iintro !> ⟨Hl, Hrb⟩
  iapply HΦ
  iframe Hl
  have hSr : st.S.lookup bi.name = r.lookup bi.name := by
    rw [← Hag _ rfl, rbData_lookup, hRB]; rfl
  have hS1 : (st.create bi).S.lookup bi.name = some ((r.lookup bi.name).getD ∅) := by
    show (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S).lookup bi.name = _
    rw [← hSr]
    rcases hc : st.S.lookup bi.name with _ | m
    · simp
    · simp [hc]
  have hrp' : rbPut (GF := GF) γ P bi.name (st.create bi).S =
      rbPart γ (· = bi.name) (rbData P (st.create bi).S) := by
    unfold rbPut; rw [hRB]; rfl
  rw [hrp']
  iapply (rbPart_congr γ _ _ _ (fun n hn => by
    subst hn; rw [rbData_lookup, hRB, GMap.lookup_insert]; exact hS1)).1 $$ Hrb

end batch

section read
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **A point read of the held shared read transaction** of the bucket `bi` whose readers' view is
`m`: `m`'s entry, under the held read (its slices bbolt's, readable while it is held:
`rtHeldF_read'`). -/
theorem read_authPoint (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView) (bv : GoString)
    (bi : BucketInfo) (m : BktData) (hhas : P.has bi) (hag : ∀ k, vOf P rv bi.name k = m.lookup k) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗
      (□ ∀ b0 : GoInterface, globalAddr bv ↦□ b0 -∗ isBucket b0 bi) ⊢
      authPointSpec ⟨go.GoType.PointerType readTx.ty, #rt⟩ bv (rtHeld γ P b rtx rv) m := by
  iintro ⟨#Hpkgb, #HB, #Hrt, #Hbk⟩
  iunfold authPointSpec
  iintro %b0 %key %kb %dq %Φ !> ⟨#Hg, Hl, Hk⟩ HΦ
  ihave #Hb0 := Hbk $$ %b0 Hg
  ihave Hnil : (slice.nil ↦*{DFrac.discard} ([] : GoString)) $$ []
  · iapply ownSlice_nil
  icases rtHeld_wf γ P b rtx rv $$ Hl with ⟨Hl, %Hwf⟩
  ihave Hl : rtHeldF γ P b rtx rv sync.rfrac.half $$ [Hl]
  · rw [← rtHeld_eq]; iexact Hl
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b rt rtx rv sync.rfrac.half b0 bi key slice.nil kb [] dq DFrac.discard (W64 0)
      (by simp) (Or.inl (by decide)) hhas) $$ [$Hpkgb $HB $Hrt $Hl $Hb0 $Hk $Hnil]
    as %ks %vs ⟨Hl, Hk, -, Hout⟩
  irevert Hout
  rw [rtRange_single P rv bi kb (W64 0) hhas Hwf, hag]
  iintro Hout
  cases hl : m.lookup kb with
  | none =>
    imod kvsOutRd_nil ⊤ rtx ks vs $$ Hout with ⟨-, #Hvs⟩
    imodintro
    iapply HΦ
    unfold pointValsA
    iframe Hk Hvs
    rw [rtHeld_eq]; iexact Hl
  | some v =>
    imod kvsOutRd_single ⊤ rtx ks vs kb v $$ Hout with ⟨%ksl, %vsl, -, -, #Hvs, #Hrv⟩
    imodintro
    iapply HΦ
    unfold pointValsA
    iframe Hk
    isplitl [Hl]
    · rw [rtHeld_eq]; iexact Hl
    iexists vsl
    iframe Hvs
    iintro !> Hl
    rw [rtHeld_eq]
    iapply rtHeldF_read' γ P b rtx rv sync.rfrac.half vsl v $$ [$Hl $Hrv]

/-- **The held shared read transaction reads the auth buckets of `r`** (`authReader`, the token
the held read), its readers' view on the three buckets `r`'s. -/
theorem read_authReader (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView)
    (r : GMap GoString BktData)
    (hhas : P.has mvcc.authBI ∧ P.has mvcc.authUsersBI ∧ P.has mvcc.authRolesBI)
    (hag : ∀ n, (n = mvcc.authBI.name ∨ n = mvcc.authUsersBI.name ∨ n = mvcc.authRolesBI.name) →
      ∀ k, vOf P rv n k = ((r.lookup n).getD ∅).lookup k) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      authReader ⟨go.GoType.PointerType readTx.ty, #rt⟩ (rtHeld γ P b rtx rv) (authDataR r) := by
  iintro ⟨#Hspkg, #Hpkgb, #HB, #Hrt⟩
  iunfold authReader
  isplitl []
  · iintro !>
    rw [show (authDataR r).auth = (r.lookup mvcc.authBI.name).getD ∅ from rfl]
    iapply (read_authPoint hUR γ P W Pk b rt rtx rv go_etcd_io.etcd.server.v3.storage.schema.Auth
      mvcc.authBI _ hhas.1 (hag _ (Or.inl rfl)))
    iframe Hpkgb HB Hrt
    iintro !> %b0 #Hg
    iapply auth_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]
  isplitl []
  · iintro !>
    rw [show (authDataR r).users = (r.lookup mvcc.authUsersBI.name).getD ∅ from rfl]
    iapply (read_authPoint hUR γ P W Pk b rt rtx rv go_etcd_io.etcd.server.v3.storage.schema.AuthUsers
      mvcc.authUsersBI _ hhas.2.1 (hag _ (Or.inr (Or.inl rfl))))
    iframe Hpkgb HB Hrt
    iintro !> %b0 #Hg
    iapply authUsers_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]
  · iintro !>
    rw [show (authDataR r).roles = (r.lookup mvcc.authRolesBI.name).getD ∅ from rfl]
    iapply (read_authPoint hUR γ P W Pk b rt rtx rv go_etcd_io.etcd.server.v3.storage.schema.AuthRoles
      mvcc.authRolesBI _ hhas.2.2 (hag _ (Or.inr (Or.inr rfl))))
    iframe Hpkgb HB Hrt
    iintro !> %b0 #Hg
    iapply authRoles_isBucket hID hName hSafe b0 $$ [$Hspkg $Hg]

/-- **The held shared read transaction with no user**: its readers' view of the users' bucket empty,
its `UnsafeForEach` over it calls nothing (`readTx.UnsafeForEach.spec`). -/
theorem read_forEachUsersEmpty (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt rtx : Loc) (rv : RView)
    (hhas : P.has mvcc.authUsersBI) (hnone : ∀ k, vOf P rv mvcc.authUsersBI.name k = none) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      forEachUsersEmpty ⟨go.GoType.PointerType readTx.ty, #rt⟩ (rtHeld γ P b rtx rv) := by
  iintro ⟨#Hspkg, #Hpkgb, #HB, #Hrt⟩
  iunfold forEachUsersEmpty
  iintro !> %bk %vis %Φ !> ⟨Hl, #Hg⟩ HΦ
  ihave #Hbk := authUsers_isBucket hID hName hSafe bk $$ [$Hspkg $Hg]
  ihave Hl : rtHeldF γ P b rtx rv sync.rfrac.half $$ [Hl]
  · rw [← rtHeld_eq]; iexact Hl
  iapply (hFE γ P W Pk b rt rtx rv sync.rfrac.half bk mvcc.authUsersBI vis hhas hnone)
    $$ [$Hpkgb $HB $Hrt $Hl $Hbk]
  iintro !> %err ⟨%Herr, Hl⟩
  iapply HΦ
  isplitr
  · ipureintro; exact Herr
  rw [rtHeld_eq]; iexact Hl

/-- **The locked batch transaction with no user**: the writer's users' bucket empty, its
`UnsafeForEach` over it calls nothing (`batchTxBuffered.UnsafeForEach.spec`). -/
theorem batch_forEachUsersEmpty (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess)
    (hhas : P.has mvcc.authUsersBI) (hnone : bktOf st.S mvcc.authUsersBI.name = ∅) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      forEachUsersEmpty ⟨go.GoType.PointerType batchTxBuffered.ty, #t⟩ (batchLocked γ P b st) := by
  iintro ⟨#Hspkg, #Hpkgb, #HB, #Ht⟩
  iunfold forEachUsersEmpty
  iintro !> %bk %vis %Φ !> ⟨Hl, #Hg⟩ HΦ
  ihave #Hbk := authUsers_isBucket hID hName hSafe bk $$ [$Hspkg $Hg]
  iapply (hFE γ P W Pk b t st bk mvcc.authUsersBI vis hhas hnone) $$ [$Hpkgb $HB $Ht $Hl $Hbk]
  iexact HΦ

end read

end schema
end EtcdGrove
end Perennial
