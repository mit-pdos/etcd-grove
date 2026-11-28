/-
**The auth realization's write side** (auth-schema-srv A6 (c), 2026-11-18): schema's batch transaction over the real
backend's (`batchTxBuffered`) meets the store's write contract (`auth.authBatchTxLkR`, `auth.authWBackendOkR`) over the
per-backend invariant (`AuthRealInv.lean`), in the claimed mode: the auth buckets are claimed, so their writes go
through the claimed part (`rbPutR`), and `Unlock`'s accessor and confirmation window move the readers' halves the
invariant keeps (`rbAcc`, `rbConf`).
- **The batch reader** (`btReader`): under the batch lock in a session `bs` (any mode), the backend's batch
  transaction is schema's `authReader` of the writer's auth buckets (`authD bs.S`), and its range of the roles'
  bucket `authRolesRange`'s.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealLife
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeDelete
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Commit
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Lock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__Unlock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafePutUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeDeleteUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafePutRole
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeDeleteRole
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetRole
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeReadAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ForceCommit
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetAllRoles
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__CreateAuthBuckets
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

/- As in `AuthRealInv`: the pool receipts' ghost maps use iris's `Pos.Countable Qp`, not the file extension's
duplicate. -/
attribute [-instance] Perennial.Fs.Qp.countable

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section ifaces
variable [GooseExts] [GoGlobalContext]

/-- The backend's batch transaction `t` as an `UnsafeReader` (schema's `authBatchTx.tx`). -/
abbrev btIface (t : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩

end ifaces

/-- The auth buckets of the writer's contents `S`. -/
def authD (S : Data) : schema.AuthData :=
  ⟨bktOf S mvcc.authBI.name, bktOf S mvcc.authUsersBI.name, bktOf S mvcc.authRolesBI.name⟩

/-! ## The batch reader -/

section reader
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- A slice of bbolt's write transaction `bs.tx` is readable under the batch lock at `bs` (with anything). -/
theorem bt_rdCap (γ : BNames) (P : BParams) (b : Loc) (bs : BSess) (c : Bool) (Z : IProp GF) (s : GoSlice)
    (v : GoString) :
    rdB γ.db bs.tx s v ⊢ schema.rdCap (iprop(batchLocked γ P b bs c ∗ Z)) s v := by
  iintro #Hr
  iunfold schema.rdCap
  iintro !> ⟨Hl, HZ⟩
  icases batchLocked_rdB γ P b bs bs s v c $$ [$Hr $Hl] with ⟨%dq, Hs, Hback⟩
  · ipureintro; rfl
  iexists dq
  iframe Hs
  iintro Hs
  ihave Hl := Hback $$ Hs
  iframe Hl HZ

theorem bt_rdCapL (γ : BNames) (P : BParams) (b : Loc) (bs : BSess) (c : Bool) (Z : IProp GF) :
    ∀ (ss : List GoSlice) (es : List Ent),
    ([∗list] x ∈ ss.zip (es.map Prod.snd), rdB (GF := GF) γ.db bs.tx x.1 x.2) ⊢
      [∗list] x ∈ ss.zip es, schema.rdCap (iprop(batchLocked γ P b bs c ∗ Z)) x.1 x.2.2
  | [], es => by
    simp only [List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: ss, [] => by
    simp only [List.map_nil, List.zip_nil_right]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: ss, e :: es => by
    simp only [List.map_cons, List.zip_cons_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iapply bt_rdCap γ P b bs c Z s e.2 $$ H1
    · iapply bt_rdCapL γ P b bs c Z ss es $$ H

/-- **A point read of the batch transaction** (`authPointSpec`): `UnsafeRange` of one key of the auth bucket
`bi` (in the table, at the global `bv`), the key's entry of the writer's contents. -/
theorem bt_point (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (bs : BSess) (c : Bool) (Z : IProp GF)
    (bv : GoString) (bi : BucketInfo)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr bv ↦□ bk ⊢ isBucket bk bi) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      schema.authPointSpec (btIface t) bv (iprop(batchLocked γ P b bs c ∗ Z)) (bktOf bs.S bi.name) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  iunfold schema.authPointSpec
  iintro %bk %key %kb %dq !> %Φ ⟨#Hg, ⟨Hl, HZ⟩, Hkey⟩ HΦ
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  iapply wp_fupd
  wp_apply (hUR γ P W Pk b t bs bk bi key slice.nil kb [] dq DFrac.discard (W64 0) (by simp) c)
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hnil] as %ks %vs ⟨Hl, Hkey, -, Hout, -⟩
  irevert Hout
  rw [cursorRange_single _ _ _ (bktEnts_sorted _), lastVal_bktEnts]
  cases hv : (bktOf bs.S bi.name).lookup kb with
  | none =>
    iintro Hout
    imod kvsOutRd_nil _ γ.db bs.tx ks vs $$ Hout with ⟨#Hks, #Hvs⟩
    imodintro
    iapply HΦ
    iframe Hkey Hl HZ
    iunfold schema.pointValsA
    iexact Hvs
  | some v =>
    iintro Hout
    imod kvsOutRd_single _ γ.db bs.tx ks vs kb v $$ Hout with ⟨%ksl, %vsl, -, -, #Hvs, #Hrv⟩
    imodintro
    iapply HΦ
    iframe Hkey Hl HZ
    iunfold schema.pointValsA
    iexists vsl
    iframe Hvs
    ihave #Hc := bt_rdCap γ P b bs c Z vsl v $$ Hrv
    iunfold schema.rdCap at Hc
    iexact Hc

/-- **The walk of `AuthUsers` of the batch transaction** (`authForEachSpec`): `UnsafeForEach` visits the writer's
entries in key order; the visitor's state after the `i`-th entry is the caller's at the first `i` entries. -/
theorem bt_forEach (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (bs : BSess) (c : Bool) (Z : IProp GF)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ bk ⊢
        isBucket bk mvcc.authUsersBI) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      schema.authForEachSpec (btIface t) go_etcd_io.etcd.server.v3.storage.schema.AuthUsers
        (iprop(batchLocked γ P b bs c ∗ Z)) (bktOf bs.S mvcc.authUsersBI.name) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  iunfold schema.authForEachSpec
  iintro %bk %fn %I !> %Φ ⟨#Hg, ⟨Hl, HZ⟩, HI, #Hvis⟩ HΦ
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  wp_apply (hFE γ P W Pk b t bs c bk mvcc.authUsersBI fn
    (fun i => I ((bktEnts (bktOf bs.S mvcc.authUsersBI.name)).take i)) (fun _ _ => iprop(False)))
    $$ [$Hb $Ht $Hl $Hbk HI] as %err ⟨Hl, Hr⟩
  · isplitl [HI]
    · simp only [List.take_zero]; iexact HI
    iintro !> %G %i %e %k %v %Hi !> %Ψ ⟨HI, Hlive, -, -, #Hv⟩ HΨ
    ihave #Hc := bt_rdCap γ P b bs c Z v e.2 $$ [Hv]
    · iunfold rdB; iright; iexact Hv
    have ht : (bktEnts (bktOf bs.S mvcc.authUsersBI.name)).take (i + 1) =
        (bktEnts (bktOf bs.S mvcc.authUsersBI.name)).take i ++ [e] := by
      rw [List.take_add_one, Hi]; rfl
    iapply Hvis $$ %((bktEnts (bktOf bs.S mvcc.authUsersBI.name)).take i) %e %k %v %Ψ [HI] [HΨ Hlive]
    · iframe HI Hc
    inext
    iintro HI
    iapply HΨ
    iframe Hlive
    ileft
    rw [ht]
    iframe HI
    ipureintro; rfl
  icases Hr with (⟨%Herr, HI⟩ | ⟨%i, -, Hf⟩)
  · iapply HΦ
    isplitr
    · ipureintro; exact Herr
    iframe Hl HZ
    iexists (bktEnts (bktOf bs.S mvcc.authUsersBI.name)).take (bktEnts (bktOf bs.S mvcc.authUsersBI.name)).length
    isplitr
    · ipureintro; rw [List.take_length]
    · simp only [mvcc.authUsersBI]; iexact HI
  · iexfalso; iexact Hf

/-- **The batch transaction's range of the roles' bucket** (`authRolesRange`). -/
theorem bt_rolesRange (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (bs : BSess) (c : Bool) (Z : IProp GF)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthRoles ↦□ bk ⊢
        isBucket bk mvcc.authRolesBI) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      schema.authRolesRange (btIface t) (iprop(batchLocked γ P b bs c ∗ Z))
        (bktOf bs.S mvcc.authRolesBI.name) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  iunfold schema.authRolesRange
  iintro %bk %key %endKey %dk %de !> %Φ ⟨#Hg, ⟨Hl, HZ⟩, Hkey, Hend⟩ HΦ
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  ihave %Hlen0 := ownSlice_len endKey de [W8 255] $$ Hend
  have Hne : (endKey = slice.nil ↔ [W8 255] = []) := by
    constructor
    · intro h; subst h; simp at Hlen0; exact absurd Hlen0.1 (by decide)
    · intro h; cases h
  wp_apply (hUR γ P W Pk b t bs bk mvcc.authRolesBI key endKey [W8 0] [W8 255] dk de (W64 (-1)) Hne c) $$ [$Hb $Ht $Hl $Hbk $Hkey $Hend] as %ks %vs ⟨Hl, Hkey, Hend, Hout, -⟩
  iunfold kvsOutRd at Hout
  iunfold rdSlices at Hout
  icases Hout with ⟨%ks', %vs', -, -, Hvs, -, -, ⟨%Hlen, Hrd⟩⟩
  iapply HΦ
  iframe Hl HZ Hkey Hend
  iexists vs'
  iframe Hvs
  isplitr
  · ipureintro
    rw [Hlen, List.length_map]; rfl
  unfold schema.rolesRangeEnts
  simp only [mvcc.authRolesBI]
  iapply bt_rdCapL γ P b bs c Z vs' _ $$ Hrd

/-- **The batch transaction is an `UnsafeReader` of the writer's auth buckets** under the token
`batchLocked … bs c ∗ Z`. -/
theorem bt_reader (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (bs : BSess) (c : Bool) (Z : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      schema.authReader (btIface t) (iprop(batchLocked γ P b bs c ∗ Z)) (authD bs.S) := by
  iintro #H
  iunfold schema.authReader
  simp only [authD]
  isplitr
  · iintro !>
    iapply bt_point hUR γ P W Pk b t bs c Z _ mvcc.authBI (schema.auth_isBucket hID hName hSafe) $$ H
  isplitr
  · iintro !>
    iapply bt_point hUR γ P W Pk b t bs c Z _ mvcc.authUsersBI
      (schema.authUsers_isBucket hID hName hSafe) $$ H
  isplitr
  · iintro !>
    iapply bt_point hUR γ P W Pk b t bs c Z _ mvcc.authRolesBI
      (schema.authRoles_isBucket hID hName hSafe) $$ H
  · iintro !>
    iapply bt_forEach hFE γ P W Pk b t bs c Z (schema.authUsers_isBucket hID hName hSafe) $$ H

end reader


/-! ## The session's kinds and `Unlock`'s windows -/

/-- A batch session's writes' kind, as the backend's kind of a bucket. -/
def kindW : auth.BkW → RbK
  | .idle => .idle
  | .puts => .put
  | .dels => .del

/-- **The session's kinds on the auth buckets** (the `auth` bucket only put into, no bucket both put into and
deleted from), and an untouched bucket's writer's contents the batch token's `x` (the readers'). -/
def tkOk (bs : BSess) (x : BktData × BktData × BktData) : Prop :=
  (bs.tk go!"auth" = .idle ∨ bs.tk go!"auth" = .put) ∧ bs.tk go!"authUsers" ≠ .mix ∧
    bs.tk go!"authRoles" ≠ .mix ∧
    (bs.tk go!"auth" = .idle → bktOf bs.S go!"auth" = x.1) ∧
    (bs.tk go!"authUsers" = .idle → bktOf bs.S go!"authUsers" = x.2.1) ∧
    (bs.tk go!"authRoles" = .idle → bktOf bs.S go!"authRoles" = x.2.2)

theorem authD_eq (S : Data) :
    authD S = ⟨bktOf S go!"auth", bktOf S go!"authUsers", bktOf S go!"authRoles"⟩ := by
  simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI,
    go_etcd_io.etcd.server.v3.storage.schema.authName, go_etcd_io.etcd.server.v3.storage.schema.authUsersName,
    go_etcd_io.etcd.server.v3.storage.schema.authRolesName]

/-- A move `Unlock` allows of a bucket neither mixed: to the writer's contents or kept; an untouched one to the
writer's contents. -/
theorem ok_move {P : BParams} {bs : BSess} {n : GoString} {o v : BktData} (hok : unlockOk P bs n o v)
    (hnm : bs.tk n ≠ .mix) (hidle : bs.tk n = .idle → bktOf bs.S n = o) :
    (v = bktOf bs.S n ∨ v = o) ∧ (bs.tk n = .idle → v = bktOf bs.S n) := by
  unfold unlockOk at hok
  rcases hok with h | ⟨-, h⟩ | ⟨h1, -⟩
  · exact ⟨Or.inl h, fun _ => h⟩
  · exact ⟨Or.inr h, fun hi => h.trans (hidle hi).symm⟩
  · exact absurd h1 hnm

/-- A move of the `auth` bucket (only put into): to the writer's contents. -/
theorem ok_auth {P : BParams} {bs : BSess} {n : GoString} {o v : BktData} (hok : unlockOk P bs n o v)
    (hk : bs.tk n = .idle ∨ bs.tk n = .put) (hidle : bs.tk n = .idle → bktOf bs.S n = o) :
    v = bktOf bs.S n := by
  unfold unlockOk at hok
  rcases hok with h | ⟨h1, h⟩ | ⟨h1, -⟩
  · exact h
  · rcases hk with hk | hk
    · exact h.trans (hidle hk).symm
    · rcases h1 with h1 | h1 <;> rw [hk] at h1 <;> cases h1
  · rcases hk with hk | hk <;> rw [hk] at h1 <;> cases h1

/-- **The view after a window**: the `auth` bucket at the writer's contents (the session's state), each other at
the writer's contents or kept with its old state. -/
theorem newView {bs : BSess} {st sa su sr su' sr' : auth.AuthState} {cs v : GoString → BktData}
    (hv : viewAt (auth.BkView.uni st) (authD bs.S))
    (hold : viewAt ⟨sa, su, sr⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩)
    (hA : v go!"auth" = bktOf bs.S go!"auth")
    (hU : (su' = st ∧ v go!"authUsers" = bktOf bs.S go!"authUsers") ∨
      (su' = su ∧ v go!"authUsers" = cs go!"authUsers"))
    (hR : (sr' = st ∧ v go!"authRoles" = bktOf bs.S go!"authRoles") ∨
      (sr' = sr ∧ v go!"authRoles" = cs go!"authRoles")) :
    viewAt ⟨st, su', sr'⟩ ⟨v go!"auth", v go!"authUsers", v go!"authRoles"⟩ := by
  rw [authD_eq] at hv
  obtain ⟨ha, hu, hr⟩ := hv
  obtain ⟨-, hu0, hr0⟩ := hold
  refine ⟨?_, ?_, ?_⟩
  · show authAt st (v go!"auth"); rw [hA]; exact ha
  · rcases hU with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · show ∃ dU, schema.usersAt su' (v go!"authUsers") dU; rw [h]; exact hu
    · show ∃ dU, schema.usersAt su' (v go!"authUsers") dU; rw [h]; exact hu0
  · rcases hR with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · show ∃ dR, schema.rolesAt sr' (v go!"authRoles") dR; rw [h]; exact hr
    · show ∃ dR, schema.rolesAt sr' (v go!"authRoles") dR; rw [h]; exact hr0

/-! ## The writes on the state's encoding -/

theorem usersAt_put {st : auth.AuthState} {m : BktData} {dU : GoString → auth.UserRec} (ur : auth.UserRec)
    (h : schema.usersAt st m dU) (hs : ur.roles.Pairwise go.GoStringLt) :
    schema.usersAt (auth.putUserRec st ur) (m.insert ur.name (auth.userEncode ur))
      (fun n => if n = ur.name then ur else dU n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n => ?_, fun n v hl => ?_⟩
  · simp only [auth.putUserRec, auth.putUser, GMap.lookup_insert_eq_iff]
    by_cases hn : ur.name = n
    · simp [hn]
    · simp only [hn, ↓reduceIte]; exact h1 n
  · simp only [GMap.lookup_insert_eq_iff] at hl
    simp only [show (auth.putUserRec st ur).users = (auth.putUser st ur.name ur.roles).users from rfl,
      auth.putUser, GMap.lookup_insert_eq_iff]
    by_cases hn : ur.name = n
    · subst hn
      simp only [↓reduceIte, Option.some.injEq] at hl
      subst hl
      simp only [↓reduceIte]
      refine ⟨trivial, trivial, trivial, hs, ?_⟩
      rw [auth.putUserRec_noPw]; simp
    · have hn' : n ≠ ur.name := fun e => hn e.symm
      simp only [hn, hn', ↓reduceIte] at hl ⊢
      obtain ⟨a, b, c, d, e⟩ := h2 n v hl
      refine ⟨a, b, c, d, ?_⟩
      rw [auth.putUserRec_noPw, if_neg hn]; exact e

theorem usersAt_del {st : auth.AuthState} {m : BktData} {dU : GoString → auth.UserRec} (name : GoString)
    (h : schema.usersAt st m dU) :
    schema.usersAt (auth.delUser st name) (m.delete name) dU := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n => ?_, fun n v hl => ?_⟩
  · simp only [auth.delUser, GMap.lookup_delete_iff]
    by_cases hn : name = n
    · simp [hn]
    · simp only [hn, ↓reduceIte]; exact h1 n
  · simp only [GMap.lookup_delete_iff] at hl
    simp only [auth.delUser, GMap.lookup_delete_iff]
    by_cases hn : name = n
    · simp [hn] at hl
    · simp only [hn, ↓reduceIte] at hl ⊢
      exact h2 n v hl

theorem rolesAt_put {st : auth.AuthState} {m : BktData} {dR : GoString → auth.RoleRec} (rr : auth.RoleRec)
    (ps : auth.Role) (h : schema.rolesAt st m dR) (hp : rr.toRole = ps ∧ ps.Pairwise auth.permLt) :
    schema.rolesAt (auth.putRole st rr.name ps) (m.insert rr.name (auth.roleEncode rr))
      (fun n => if n = rr.name then rr else dR n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n => ?_, fun n v hl => ?_⟩
  · simp only [auth.putRole, GMap.lookup_insert_eq_iff]
    by_cases hn : rr.name = n
    · simp [hn]
    · simp only [hn, ↓reduceIte]; exact h1 n
  · simp only [GMap.lookup_insert_eq_iff] at hl
    simp only [auth.putRole, GMap.lookup_insert_eq_iff]
    by_cases hn : rr.name = n
    · subst hn
      simp only [↓reduceIte, Option.some.injEq] at hl
      subst hl
      simp only [↓reduceIte]
      simpa using hp
    · have hn' : n ≠ rr.name := fun e => hn e.symm
      simp only [hn, hn', ↓reduceIte] at hl ⊢
      exact h2 n v hl

theorem rolesAt_del {st : auth.AuthState} {m : BktData} {dR : GoString → auth.RoleRec} (name : GoString)
    (h : schema.rolesAt st m dR) :
    schema.rolesAt { st with roles := GMap.delete name st.roles } (m.delete name) dR := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n => ?_, fun n v hl => ?_⟩
  · simp only [GMap.lookup_delete_iff]
    by_cases hn : name = n
    · simp [hn]
    · simp only [hn, ↓reduceIte]; exact h1 n
  · simp only [GMap.lookup_delete_iff] at hl
    simp only [GMap.lookup_delete_iff]
    by_cases hn : name = n
    · simp [hn] at hl
    · simp only [hn, ↓reduceIte] at hl ⊢
      exact h2 n v hl

theorem authAt_enabled {st : auth.AuthState} {ca : BktData} (b : Bool) (h : authAt st ca) :
    authAt { st with enabled := b } (ca.insert schema.authEnabledKey (if b then [W8 1] else [W8 0])) := by
  obtain ⟨he, hr, hw⟩ := h
  have hne : schema.authEnabledKey ≠ schema.authRevisionKey := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [schema.enabledOf, GMap.lookup_insert_eq_iff, ↓reduceIte]
    cases b <;> decide
  · simp only [schema.revisionOf, GMap.lookup_insert_eq_iff, hne, ↓reduceIte] at hr ⊢
    exact hr
  · intro v hv
    simp only [GMap.lookup_insert_eq_iff, hne, ↓reduceIte] at hv
    exact hw v hv

theorem authAt_revision {st : auth.AuthState} {ca : BktData} (rev : w64) (h : authAt st ca) :
    authAt { st with revision := uint.nat rev } (ca.insert schema.authRevisionKey (u64Be rev)) := by
  obtain ⟨he, hr, hw⟩ := h
  have hne : schema.authRevisionKey ≠ schema.authEnabledKey := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [schema.enabledOf, GMap.lookup_insert_eq_iff, hne, ↓reduceIte] at he ⊢
    exact he
  · simp only [schema.revisionOf, GMap.lookup_insert_eq_iff, ↓reduceIte, beToU64_u64Be]
  · intro v hv
    simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.some.injEq] at hv
    subst hv; exact u64Be_length rev

/-! ## The lock token's facts -/

theorem authBI_name : mvcc.authBI.name = go!"auth" := rfl
theorem authUsersBI_name : mvcc.authUsersBI.name = go!"authUsers" := rfl
theorem authRolesBI_name : mvcc.authRolesBI.name = go!"authRoles" := rfl

/-- **The lock token's facts** of a session `bs` at the state `st`, the readers' contents `x` (the batch token), the
session's writes `w` and the receipts `k` held: out of the hook's window; nothing the readers see changed
(`viewSame`: the auth buckets are hook buckets); the claimed writes on the auth buckets; the pending writes bounded by
the receipts; the kinds (`auth` only put into, the others as `w`); an untouched bucket's writer's contents the
readers'; the writer's auth buckets hold `st`. -/
structure LkOk (d : mvcc.KBReal) (bs : BSess) (st : auth.AuthState) (x : BktData × BktData × BktData)
    (w : auth.AuthSess) (k : Nat) : Prop where
  hw : bs.cnt.hw = false
  vs : viewSame d.P bs
  cw : ∀ n, bs.cw n = true → n ∈ authBktL
  pend : sint.Z bs.pend < sint.Z d.P.limit + k + 3
  ka : bs.tk go!"auth" = .idle ∨ bs.tk go!"auth" = .put
  ku : bs.tk go!"authUsers" = kindW w.users
  kr : bs.tk go!"authRoles" = kindW w.roles
  ia : bs.tk go!"auth" = .idle → bktOf bs.S go!"auth" = x.1
  iu : bs.tk go!"authUsers" = .idle → bktOf bs.S go!"authUsers" = x.2.1
  ir : bs.tk go!"authRoles" = .idle → bktOf bs.S go!"authRoles" = x.2.2
  view : viewAt (auth.BkView.uni st) (authD bs.S)

theorem kindW_ne_mix (b : auth.BkW) : kindW b ≠ .mix := by cases b <;> simp [kindW]

theorem LkOk.tkOk {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (h : LkOk d bs st x w k) : tkOk bs x :=
  ⟨h.ka, by rw [h.ku]; exact kindW_ne_mix _, by rw [h.kr]; exact kindW_ne_mix _, h.ia, h.iu, h.ir⟩

theorem pend_succ {p lim : w64} {k : Nat} (h : sint.Z p < sint.Z lim + k + 3) (hb : sint.Z p + 1 < 2 ^ 58) :
    sint.Z (p + W64 1) < sint.Z lim + (k + 1 : Nat) + 3 := by
  have : sint.Z (p + W64 1) = sint.Z p + 1 := by word
  push_cast; omega

theorem auth_ne_users : go!"auth" ≠ go!"authUsers" := by decide
theorem auth_ne_roles : go!"auth" ≠ go!"authRoles" := by decide
theorem users_ne_roles : go!"authUsers" ≠ go!"authRoles" := by decide

theorem hb_auth (d : mvcc.KBReal) (n : GoString) (h : n ∈ authBktL) : d.P.HB n = true := by
  simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [mvcc.KBReal.P, go_etcd_io.etcd.server.v3.storage.schema.keyName]

/-- The data's other buckets after a change of one. -/
theorem bktOf_ins_ne (S : Data) (n m : GoString) (b : BktData) (h : n ≠ m) :
    bktOf (S.insert n b) m = bktOf S m := by
  unfold bktOf; rw [GMap.lookup_insert_ne _ _ h]

theorem bktOf_ins (S : Data) (n : GoString) (b : BktData) : bktOf (S.insert n b) n = b := by
  unfold bktOf; rw [GMap.lookup_insert]; rfl

/-- **A put into the users' bucket** keeps the lock token's facts at the state with the user. -/
theorem lkOk_putUser {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (hWf : d.P.Wf) (hhas : d.P.has mvcc.authUsersBI) (ur : auth.UserRec)
    (h : LkOk d bs st x w k) (hb : sint.Z bs.pend + 1 < 2 ^ 58) (hw : w.users ≠ .dels)
    (hs : ur.roles.Pairwise go.GoStringLt) :
    LkOk d (bs.put mvcc.authUsersBI ur.name (auth.userEncode ur) false true) (auth.putUserRec st ur) x
      { w with users := .puts } (k + 1) where
  hw := h.hw
  vs := mvcc.viewSame_putHB hWf (hb_auth d _ (by simp [authBktL, authUsersBI_name])) hhas h.vs
  cw := fun n hn => by
    simp only [BSess.put, ↓reduceIte, cwAdd] at hn
    split at hn
    · rename_i he; subst he; simp [authBktL, authUsersBI_name]
    · exact h.cw n hn
  pend := pend_succ h.pend hb
  ka := by simp only [BSess.put, tkSet, authUsersBI_name, if_neg auth_ne_users]; exact h.ka
  ku := by
    simp only [BSess.put, tkSet, authUsersBI_name, ↓reduceIte, h.ku, kindW]
    cases hu : w.users <;> simp_all [RbK.join]
  kr := by simp only [BSess.put, tkSet, authUsersBI_name, if_neg users_ne_roles.symm]; exact h.kr
  ia := by
    simp only [BSess.put, tkSet, authUsersBI_name, if_neg auth_ne_users]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_users.symm]; exact h.ia hi
  iu := by
    simp only [BSess.put, tkSet, authUsersBI_name, ↓reduceIte, h.ku]
    intro hi; cases hu : w.users <;> simp_all [RbK.join, kindW]
  ir := by
    simp only [BSess.put, tkSet, authUsersBI_name, if_neg users_ne_roles.symm]
    intro hi; rw [bktOf_ins_ne _ _ _ _ users_ne_roles]; exact h.ir hi
  view := by
    have hv := h.view
    rw [authD_eq] at hv ⊢
    obtain ⟨ha, ⟨dU, hu⟩, hr⟩ := hv
    simp only [BSess.put, authUsersBI_name]
    rw [bktOf_ins_ne _ _ _ _ auth_ne_users.symm, bktOf_ins_ne _ _ _ _ users_ne_roles, bktOf_ins]
    exact ⟨ha, ⟨_, usersAt_put ur hu hs⟩, hr⟩

/-- **A delete from the users' bucket.** -/
theorem lkOk_delUser {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (name : GoString)
    (h : LkOk d bs st x w k) (hb : sint.Z bs.pend + 1 < 2 ^ 58) (hw : w.users ≠ .puts) :
    LkOk d (bs.del mvcc.authUsersBI name true) (auth.delUser st name) x { w with users := .dels } (k + 1) where
  hw := h.hw
  vs := mvcc.viewSame_del (hb_auth d _ (by simp [authBktL, authUsersBI_name])) h.vs
  cw := fun n hn => by
    simp only [BSess.del, ↓reduceIte, cwAdd] at hn
    split at hn
    · rename_i he; subst he; simp [authBktL, authUsersBI_name]
    · exact h.cw n hn
  pend := pend_succ h.pend hb
  ka := by simp only [BSess.del, tkSet, authUsersBI_name, if_neg auth_ne_users]; exact h.ka
  ku := by
    simp only [BSess.del, tkSet, authUsersBI_name, ↓reduceIte, h.ku, kindW]
    cases hu : w.users <;> simp_all [RbK.join]
  kr := by simp only [BSess.del, tkSet, authUsersBI_name, if_neg users_ne_roles.symm]; exact h.kr
  ia := by
    simp only [BSess.del, tkSet, authUsersBI_name, if_neg auth_ne_users]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_users.symm]; exact h.ia hi
  iu := by
    simp only [BSess.del, tkSet, authUsersBI_name, ↓reduceIte, h.ku]
    intro hi; cases hu : w.users <;> simp_all [RbK.join, kindW]
  ir := by
    simp only [BSess.del, tkSet, authUsersBI_name, if_neg users_ne_roles.symm]
    intro hi; rw [bktOf_ins_ne _ _ _ _ users_ne_roles]; exact h.ir hi
  view := by
    have hv := h.view
    rw [authD_eq] at hv ⊢
    obtain ⟨ha, ⟨dU, hu⟩, hr⟩ := hv
    simp only [BSess.del, authUsersBI_name]
    rw [bktOf_ins_ne _ _ _ _ auth_ne_users.symm, bktOf_ins_ne _ _ _ _ users_ne_roles, bktOf_ins]
    exact ⟨ha, ⟨_, usersAt_del name hu⟩, hr⟩

/-- **A put into the roles' bucket.** -/
theorem lkOk_putRole {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (hWf : d.P.Wf) (hhas : d.P.has mvcc.authRolesBI) (rr : auth.RoleRec)
    (ps : auth.Role) (h : LkOk d bs st x w k) (hb : sint.Z bs.pend + 1 < 2 ^ 58) (hw : w.roles ≠ .dels)
    (hp : rr.toRole = ps ∧ ps.Pairwise auth.permLt) :
    LkOk d (bs.put mvcc.authRolesBI rr.name (auth.roleEncode rr) false true) (auth.putRole st rr.name ps) x
      { w with roles := .puts } (k + 1) where
  hw := h.hw
  vs := mvcc.viewSame_putHB hWf (hb_auth d _ (by simp [authBktL, authRolesBI_name])) hhas h.vs
  cw := fun n hn => by
    simp only [BSess.put, ↓reduceIte, cwAdd] at hn
    split at hn
    · rename_i he; subst he; simp [authBktL, authRolesBI_name]
    · exact h.cw n hn
  pend := pend_succ h.pend hb
  ka := by simp only [BSess.put, tkSet, authRolesBI_name, if_neg auth_ne_roles]; exact h.ka
  ku := by simp only [BSess.put, tkSet, authRolesBI_name, if_neg users_ne_roles]; exact h.ku
  kr := by
    simp only [BSess.put, tkSet, authRolesBI_name, ↓reduceIte, h.kr, kindW]
    cases hu : w.roles <;> simp_all [RbK.join]
  ia := by
    simp only [BSess.put, tkSet, authRolesBI_name, if_neg auth_ne_roles]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_roles.symm]; exact h.ia hi
  iu := by
    simp only [BSess.put, tkSet, authRolesBI_name, if_neg users_ne_roles]
    intro hi; rw [bktOf_ins_ne _ _ _ _ users_ne_roles.symm]; exact h.iu hi
  ir := by
    simp only [BSess.put, tkSet, authRolesBI_name, ↓reduceIte, h.kr]
    intro hi; cases hu : w.roles <;> simp_all [RbK.join, kindW]
  view := by
    have hv := h.view
    rw [authD_eq] at hv ⊢
    obtain ⟨ha, hu, ⟨dR, hr⟩⟩ := hv
    simp only [BSess.put, authRolesBI_name]
    rw [bktOf_ins_ne _ _ _ _ auth_ne_roles.symm, bktOf_ins_ne _ _ _ _ users_ne_roles.symm, bktOf_ins]
    exact ⟨ha, hu, ⟨_, rolesAt_put rr ps hr hp⟩⟩

/-- **A delete from the roles' bucket.** -/
theorem lkOk_delRole {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (name : GoString)
    (h : LkOk d bs st x w k) (hb : sint.Z bs.pend + 1 < 2 ^ 58) (hw : w.roles ≠ .puts) :
    LkOk d (bs.del mvcc.authRolesBI name true) { st with roles := GMap.delete name st.roles } x
      { w with roles := .dels } (k + 1) where
  hw := h.hw
  vs := mvcc.viewSame_del (hb_auth d _ (by simp [authBktL, authRolesBI_name])) h.vs
  cw := fun n hn => by
    simp only [BSess.del, ↓reduceIte, cwAdd] at hn
    split at hn
    · rename_i he; subst he; simp [authBktL, authRolesBI_name]
    · exact h.cw n hn
  pend := pend_succ h.pend hb
  ka := by simp only [BSess.del, tkSet, authRolesBI_name, if_neg auth_ne_roles]; exact h.ka
  ku := by simp only [BSess.del, tkSet, authRolesBI_name, if_neg users_ne_roles]; exact h.ku
  kr := by
    simp only [BSess.del, tkSet, authRolesBI_name, ↓reduceIte, h.kr, kindW]
    cases hu : w.roles <;> simp_all [RbK.join]
  ia := by
    simp only [BSess.del, tkSet, authRolesBI_name, if_neg auth_ne_roles]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_roles.symm]; exact h.ia hi
  iu := by
    simp only [BSess.del, tkSet, authRolesBI_name, if_neg users_ne_roles]
    intro hi; rw [bktOf_ins_ne _ _ _ _ users_ne_roles.symm]; exact h.iu hi
  ir := by
    simp only [BSess.del, tkSet, authRolesBI_name, ↓reduceIte, h.kr]
    intro hi; cases hu : w.roles <;> simp_all [RbK.join, kindW]
  view := by
    have hv := h.view
    rw [authD_eq] at hv ⊢
    obtain ⟨ha, hu, ⟨dR, hr⟩⟩ := hv
    simp only [BSess.del, authRolesBI_name]
    rw [bktOf_ins_ne _ _ _ _ auth_ne_roles.symm, bktOf_ins_ne _ _ _ _ users_ne_roles.symm, bktOf_ins]
    exact ⟨ha, hu, ⟨_, rolesAt_del name hr⟩⟩

/-- **A put into the `auth` bucket** of a key and a value that keep its facts, at the state `st'` with `st`'s users and
roles. -/
theorem lkOk_putAuth {d : mvcc.KBReal} {bs : BSess} {st st' : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (hWf : d.P.Wf) (hhas : d.P.has mvcc.authBI) (kb vb : GoString)
    (h : LkOk d bs st x w k) (hb : sint.Z bs.pend + 1 < 2 ^ 58)
    (hu : st'.users = st.users) (hr : st'.roles = st.roles) (hn : st'.noPwUsers = st.noPwUsers)
    (ha : authAt st (bktOf bs.S go!"auth") → authAt st' ((bktOf bs.S go!"auth").insert kb vb)) :
    LkOk d (bs.put mvcc.authBI kb vb false true) st' x w (k + 1) where
  hw := h.hw
  vs := mvcc.viewSame_putHB hWf (hb_auth d _ (by simp [authBktL, authBI_name])) hhas h.vs
  cw := fun n hn => by
    simp only [BSess.put, ↓reduceIte, cwAdd] at hn
    split at hn
    · rename_i he; subst he; simp [authBktL, authBI_name]
    · exact h.cw n hn
  pend := pend_succ h.pend hb
  ka := by
    simp only [BSess.put, tkSet, authBI_name, ↓reduceIte]
    rcases h.ka with h1 | h1 <;> rw [h1] <;> simp [RbK.join]
  ku := by simp only [BSess.put, tkSet, authBI_name, if_neg auth_ne_users.symm]; exact h.ku
  kr := by simp only [BSess.put, tkSet, authBI_name, if_neg auth_ne_roles.symm]; exact h.kr
  ia := by
    simp only [BSess.put, tkSet, authBI_name, ↓reduceIte]
    intro hi; rcases h.ka with h1 | h1 <;> rw [h1] at hi <;> simp [RbK.join] at hi
  iu := by
    simp only [BSess.put, tkSet, authBI_name, if_neg auth_ne_users.symm]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_users]; exact h.iu hi
  ir := by
    simp only [BSess.put, tkSet, authBI_name, if_neg auth_ne_roles.symm]
    intro hi; rw [bktOf_ins_ne _ _ _ _ auth_ne_roles]; exact h.ir hi
  view := by
    have hv := h.view
    rw [authD_eq] at hv ⊢
    obtain ⟨ha0, ⟨dU, hu0⟩, ⟨dR, hr0⟩⟩ := hv
    simp only [BSess.put, authBI_name]
    rw [bktOf_ins_ne _ _ _ _ auth_ne_users, bktOf_ins_ne _ _ _ _ auth_ne_roles, bktOf_ins]
    refine ⟨ha ha0, ⟨dU, ?_⟩, ⟨dR, ?_⟩⟩
    · show schema.usersAt st' _ dU; unfold schema.usersAt auth.AuthState.noPw; rw [hu, hn]; exact hu0
    · show schema.rolesAt st' _ dR; unfold schema.rolesAt; rw [hr]; exact hr0

theorem hk_auth (d : mvcc.KBReal) (n k : GoString) (h : n ∈ authBktL) : d.P.HK n k = false := by
  simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [mvcc.KBReal.P, go_etcd_io.etcd.server.v3.storage.schema.metaName]

theorem sb_auth (d : mvcc.KBReal) (n : GoString) (h : n ∈ authBktL) : d.P.SB n = false := by
  simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [mvcc.KBReal.P, go_etcd_io.etcd.server.v3.storage.schema.keyName]

theorem fk_auth (n k : GoString) (h : n ∈ authBktL) : ¬ fkKey n k := by
  simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at h
  rintro ⟨hm, -⟩
  rcases h with rfl | rfl | rfl <;> simp at hm

theorem hkb_auth (d : mvcc.KBReal) (n k : GoString) (h : n ∈ authBktL) : d.P.hk n k = false := by
  unfold BParams.hk; rw [hk_auth d n k h]; simp


section wr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

instance stateAt_timeless (γa : auth.AuthNames) (i : Nat) (st : auth.AuthState) :
    Timeless (auth.authStateAt (GF := GF) γa i st) := by
  unfold auth.authStateAt monoListIdxOwn; infer_instance

/-- The client's halves of the auth buckets, as three. -/
theorem rbRd3 (γB : BNames) (f : GoString → BktData) :
    ([∗list] n ∈ authBktL, rbRd (GF := GF) γB n (1 : Qp).half (f n)) ⊣⊢
      iprop(rbRd γB go!"auth" (1 : Qp).half (f go!"auth") ∗
        rbRd γB go!"authUsers" (1 : Qp).half (f go!"authUsers") ∗
        rbRd γB go!"authRoles" (1 : Qp).half (f go!"authRoles")) := by
  unfold authBktL
  constructor
  · iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, -⟩
    iframe H1 H2 H3
  · iintro ⟨H1, H2, H3⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply BigSepL.bigSepL_cons.2
    iframe H2
    iapply BigSepL.bigSepL_cons.2
    iframe H3
    iapply BigSepL.bigSepL_nil.2
    iempintro

/-- The lock's quarter of the history records its last state. -/
theorem lockQ_rec (γa : auth.AuthNames) (hs : List auth.AuthState) (st : auth.AuthState)
    (h : hs.getLast? = some st) :
    auth.authLockQ (GF := GF) γa hs ⊢ auth.authLockQ γa hs ∗ auth.authStateAt γa (hs.length - 1) st := by
  unfold auth.authLockQ auth.authStateAt
  iintro ⟨H, %Hk⟩
  ihave #Hlb := monoListLbOwn_get γa.hist _ hs $$ H
  have hi : hs[hs.length - 1]? = some st := by rw [List.getLast?_eq_getElem?] at h; exact h
  iframe H
  isplitr
  · ipureintro; exact Hk
  isplitl []
  · iapply (monoListIdxOwn_get (hs.length - 1) st hi) $$ Hlb
  · ipureintro; exact Hk st (List.mem_of_getLast? h)

/-- A recorded state is in the history the lock's quarter is of. -/
theorem lockQ_idx (γa : auth.AuthNames) (hs : List auth.AuthState) (j : Nat) (s : auth.AuthState) :
    auth.authLockQ (GF := GF) γa hs ∗ auth.authStateAt γa j s ⊢ auth.authLockQ γa hs ∗ ⌜j < hs.length⌝ := by
  unfold auth.authLockQ auth.authStateAt
  iintro ⟨⟨H, %Hk⟩, ⟨Hi, -⟩⟩
  ihave %Hl := mono_list_auth_idx_lookup γa.hist _ hs j s $$ H Hi
  iframe H
  isplitr
  · ipureintro; exact Hk
  · ipureintro; exact (List.getElem?_eq_some_iff.1 Hl).1

/-- One of two recorded states, as the bucket's new contents say. -/
theorem pickAt (γa : auth.AuthNames) (L jo : Nat) (st so : auth.AuthState) (vn wn vo : BktData)
    (h : vn = wn ∨ vn = vo) :
    auth.authStateAt (GF := GF) γa L st ∗ auth.authStateAt γa jo so ⊢
      ∃ (s : auth.AuthState) (j : Nat), auth.authStateAt γa j s ∗
        ⌜(s = st ∧ j = L ∧ vn = wn) ∨ (s = so ∧ j = jo ∧ vn = vo)⌝ := by
  iintro ⟨#H1, #H2⟩
  rcases h with h | h
  · iexists st, L; iframe H1; ipureintro; exact Or.inl ⟨rfl, rfl, h⟩
  · iexists so, jo; iframe H2; ipureintro; exact Or.inr ⟨rfl, rfl, h⟩

/-- Half the batch token and the whole one: false. -/
theorem bkTok_half_one (γ : RNames) (x y : BktData × BktData × BktData) :
    bkTok (GF := GF) γ (1 : Qp).half x ∗ bkTok γ 1 y ⊢ False := by
  unfold bkTok
  iintro ⟨H1, H2⟩
  ihave %h := ghostVar_valid_2 _ _ _ _ _ $$ H2 H1
  exfalso; exact one_add_not_le _ h.1

/-- **`Unlock`'s resource for the windows** of a session `bs` at the state `st`, the last of `hs`: half the batch
token at the readers' contents `x` (the invariant's batch branch holds the other half), the lock's quarter of the
history (to record `st`), and the session's kinds. -/
def unRr (γ : RNames) (bs : BSess) (st : auth.AuthState) (hs : List auth.AuthState) : IProp GF :=
  iprop(∃ x, bkTok γ (1 : Qp).half x ∗ auth.authLockQ γ.γa hs ∗ ⌜hs.getLast? = some st ∧ tkOk bs x⌝)

/-- **`Unlock`'s resource after its confirmation**: the batch token at the writer's contents. -/
def unRr' (γ : RNames) (bs : BSess) (st : auth.AuthState) (hs : List auth.AuthState) : IProp GF :=
  iprop(bkTok γ (1 : Qp).half (csT (fun n => bktOf bs.S n)) ∗ auth.authLockQ γ.γa hs ∗
    ⌜hs.getLast? = some st⌝)

/-- **`Unlock`'s window** (`rbAcc`): with the invariant opened around it, the readers' halves of the auth buckets
move as `Unlock` allows; the `auth` bucket to the writer's contents (the session's state, recorded at the history's
last index), each other to the writer's contents (recorded likewise) or kept with its recorded state. -/
theorem real_acc (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (bs : BSess) (st : auth.AuthState)
    (hs : List auth.AuthState) (hv : viewAt (auth.BkView.uni st) (authD bs.S)) :
    realInv (GF := GF) γ d s0 q0 ⊢
      rbAcc d.γB authBktL (unlockOk d.P bs) (unRr γ bs st hs) (⊤ ∖ ↑authRealN) := by
  iintro #Hinv
  unfold rbAcc
  iintro !> HR
  iunfold unRr at HR
  icases HR with ⟨%x, Hx, Hlq, %Hh⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, HT, >Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, >Hbt⟩)
  rotate_left
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ x y $$ [$Hx $Hbt]
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ x y $$ [$Hx $Hbt]
  icases Hb with (Hid | Hbb)
  · iunfold bkIdle at Hid
    icases Hid with ⟨%hs', %rc, %w, -, -, >Hbt, -, -, -⟩
    iexfalso; iapply bkTok_half_one γ x _ $$ [$Hx $Hbt]
  iunfold bkBatch at Hbb
  icases Hbb with ⟨HT, >Hbt⟩
  iunfold bkTok at Hx Hbt
  icombine Hx Hbt gives %Hxe
  obtain ⟨-, rfl⟩ := Hxe
  iunfold bkCommon at Hc
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >%Hv⟩
  imodintro
  iexists cs
  isplitl [Ha Hu Hr']
  · iapply (rbRd3 d.γB cs).2
    iframe Ha Hu Hr'
  iintro %v %Hok Hv3
  icases (rbRd3 d.γB v).1 $$ Hv3 with ⟨Ha, Hu, Hr'⟩
  obtain ⟨hl, htk⟩ := Hh
  obtain ⟨hka, hnu, hnr, hia, hiu, hir⟩ := htk
  have hA := ok_auth (Hok go!"auth" (by simp [authBktL])) hka hia
  have hU := ok_move (Hok go!"authUsers" (by simp [authBktL])) hnu hiu
  have hR := ok_move (Hok go!"authRoles" (by simp [authBktL])) hnr hir
  icases lockQ_rec γ.γa hs st hl $$ Hlq with ⟨Hlq, #HsL⟩
  icases lockQ_idx γ.γa hs ju su $$ [$Hlq $Hsu] with ⟨Hlq, %Hju⟩
  icases lockQ_idx γ.γa hs jr sr $$ [$Hlq $Hsr] with ⟨Hlq, %Hjr⟩
  icases pickAt γ.γa (hs.length - 1) ju st su (v go!"authUsers") (bktOf bs.S go!"authUsers")
    (cs go!"authUsers") hU.1 $$ [$HsL $Hsu] with ⟨%su', %ju', #Hsu', %Hpu⟩
  icases pickAt γ.γa (hs.length - 1) jr st sr (v go!"authRoles") (bktOf bs.S go!"authRoles")
    (cs go!"authRoles") hR.1 $$ [$HsL $Hsr] with ⟨%sr', %jr', #Hsr', %Hpr⟩
  imod ghostVar_update_halves (csT v) γ.γk (csT cs) (csT cs) $$ Hx Hbt with ⟨Hx, Hbt⟩
  have hview := newView (sa := sa) (su := su) (sr := sr) (cs := cs) hv Hv.1 hA
    (by rcases Hpu with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨h1, h3⟩)
    (by rcases Hpr with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨h1, h3⟩)
  imod Hclose $$ [Ha Hu Hr' Hs Hr Hp HT Hbt] with -
  · inext
    iunfold realSt
    iexists v, st, su', sr', hs.length - 1, ju', jr', p
    isplitl [Ha Hu Hr']
    · iunfold bkCommon
      iframe Ha Hu Hr'
      iframe #
      ipureintro
      obtain ⟨-, -, -, hpu, hpr⟩ := Hv
      refine ⟨hview, ?_, ?_, ?_, ?_⟩
      · rcases Hpu with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
      · rcases Hpr with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
      · rcases Hpu with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
      · rcases Hpr with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    ileft
    iframe Hs Hr Hp
    iright
    iunfold bkBatch
    iframe HT
    iunfold bkTok
    iexact Hbt
  imodintro
  iunfold unRr
  iexists csT v
  iunfold bkTok
  iframe Hx Hlq
  ipureintro
  refine ⟨hl, hka, hnu, hnr, fun _ => hA.symm, ?_, ?_⟩
  · intro h; exact (hU.2 h).symm
  · intro h; exact (hR.2 h).symm

/-- The view with every bucket at the writer's contents, which hold the session's state. -/
theorem viewAt_writer {bs : BSess} {st : auth.AuthState} {cs : GoString → BktData}
    (hv : viewAt (auth.BkView.uni st) (authD bs.S)) (ha : cs go!"auth" = bktOf bs.S go!"auth")
    (hu : cs go!"authUsers" = bktOf bs.S go!"authUsers") (hr : cs go!"authRoles" = bktOf bs.S go!"authRoles") :
    viewAt ⟨st, st, st⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ := by
  rw [authD_eq] at hv
  rw [ha, hu, hr]
  exact hv

/-- **`Unlock`'s confirmation** (`rbConf`): the readers' halves of the auth buckets are at the writer's contents,
which hold the session's state: every bucket recorded at it, at the history's last index; the batch token at
the writer's contents. -/
theorem real_conf (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (bs : BSess) (st : auth.AuthState)
    (hs : List auth.AuthState) (hv : viewAt (auth.BkView.uni st) (authD bs.S)) :
    realInv (GF := GF) γ d s0 q0 ⊢
      rbConf d.γB authBktL (fun n => bktOf bs.S n) (unRr γ bs st hs) (unRr' γ bs st hs) (⊤ ∖ ↑authRealN) := by
  iintro #Hinv
  unfold rbConf
  iintro HR
  iunfold unRr at HR
  icases HR with ⟨%x, Hx, Hlq, %Hh⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, HT, >Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, >Hbt⟩)
  rotate_left
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ x y $$ [$Hx $Hbt]
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ x y $$ [$Hx $Hbt]
  icases Hb with (Hid | Hbb)
  · iunfold bkIdle at Hid
    icases Hid with ⟨%hs', %rc, %w, -, -, >Hbt, -, -, -⟩
    iexfalso; iapply bkTok_half_one γ x _ $$ [$Hx $Hbt]
  iunfold bkBatch at Hbb
  icases Hbb with ⟨HT, >Hbt⟩
  iunfold bkTok at Hx Hbt
  icombine Hx Hbt gives %Hxe
  obtain ⟨-, rfl⟩ := Hxe
  iunfold bkCommon at Hc
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >%Hv⟩
  imodintro
  iexists cs
  isplitl [Ha Hu Hr']
  · iapply (rbRd3 d.γB cs).2
    iframe Ha Hu Hr'
  iintro %Hcs Hv3
  icases (rbRd3 d.γB cs).1 $$ Hv3 with ⟨Ha, Hu, Hr'⟩
  have ha := Hcs go!"auth" (by simp [authBktL])
  have hu := Hcs go!"authUsers" (by simp [authBktL])
  have hr := Hcs go!"authRoles" (by simp [authBktL])
  have hcsT : csT cs = csT (fun n => bktOf bs.S n) := by simp only [csT, ha, hu, hr]
  icases lockQ_rec γ.γa hs st Hh.1 $$ Hlq with ⟨Hlq, #HsL⟩
  icases lockQ_idx γ.γa hs ju su $$ [$Hlq $Hsu] with ⟨Hlq, %Hju⟩
  imod Hclose $$ [Ha Hu Hr' Hs Hr Hp HT Hbt] with -
  · inext
    iunfold realSt
    iexists cs, st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr']
    · iunfold bkCommon
      iframe Ha Hu Hr'
      iframe #
      ipureintro
      obtain ⟨-, -, -, hpu, -⟩ := Hv
      exact ⟨viewAt_writer hv ha hu hr, Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
    ileft
    iframe Hs Hr Hp
    iright
    iunfold bkBatch
    iframe HT
    iunfold bkTok
    iexact Hbt
  imodintro
  iunfold unRr'
  rw [← hcsT]
  iunfold bkTok
  iframe Hx Hlq
  ipureintro; exact Hh.1

theorem rb_auth (d : mvcc.KBReal) : ∀ n, n ∈ authBktL → d.P.RB n = true := by
  intro n h
  simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> simp [mvcc.KBReal.P, mvcc.restBuckets]

theorem bktOf_rbData (P : BParams) (S : Data) (n : GoString) (h : P.RB n = true) :
    bktOf (rbData P S) n = bktOf S n := by
  unfold bktOf; rw [rbData_lookup, h]; rfl

/-- **A batch begins** (`Lock`'s ghost step, before `LockInsideApply`): the write token deposited, the idle branch's
lock share of the history, claimed part, half the batch token, session token and the rest of the open share taken
out; the buckets are at the history's last state. -/
theorem real_borrow (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ auth.authWTok γ.γc ⊢
      |={⊤}=> ∃ (cs : GoString → BktData) (hs : List auth.AuthState) (rc : GMap GoString BktData)
        (w : auth.AuthSess) (st : auth.AuthState),
        auth.authLockQ γ.γa hs ∗ rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗
        bkTok γ (1 : Qp).half (csT cs) ∗ bkSw γ 1 w ∗ bOpen d.γB q0 ∗
        ⌜hs.getLast? = some st ∧ viewAt ⟨st, st, st⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ ∧
          ∀ n, n ∈ authBktL → bktOf rc n = cs n⌝ := by
  iintro ⟨#Hinv, HT⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, >HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, >HT', Hbt⟩)
  rotate_left
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  icases Hb with (Hid | Hbb)
  rotate_left
  · iunfold bkBatch at Hbb
    icases Hbb with ⟨>HT', -⟩
    iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  iunfold bkIdle at Hid
  icases Hid with ⟨%hs, %rc, %w, >Hlq, >Hro, >Hbt, >Hsw, >Hq, >%Hid⟩
  obtain ⟨hl, hu, hr, -, -, -, hcs⟩ := Hid
  iunfold bkCommon at Hc
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >%Hv⟩
  iunfold bkTok at Hbt
  icases (ghostVar_split_half γ.γk 1 (csT cs)).1 $$ Hbt with ⟨Hb1, Hb2⟩
  imod Hclose $$ [Ha Hu Hr' Hs Hr Hp HT Hb1] with -
  · inext
    iunfold realSt
    iexists cs, sa, su, sr, ja, ju, jr, p
    isplitl [Ha Hu Hr']
    · iunfold bkCommon
      iframe Ha Hu Hr'
      iframe #
      ipureintro; exact Hv
    ileft
    iframe Hs Hr Hp
    iright
    iunfold bkBatch
    iframe HT
    iunfold bkTok
    iexact Hb1
  imodintro
  iexists cs, hs, rc, w, sa
  iframe Hlq Hro Hsw Hq
  iunfold bkTok
  iframe Hb2
  ipureintro
  refine ⟨hl, ?_, hcs⟩
  have h := Hv.1
  rw [hu, hr] at h
  exact h

/-- **A batch ends** (after `Unlock`'s confirmation and `Commit`): the batch token's halves at the writer's
contents, which hold the session's state, the last of the lock's share of the history; the buckets idle at it, each
recorded at the history's last index; the write token taken out. -/
theorem real_return (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (bs : BSess) (st : auth.AuthState)
    (hs : List auth.AuthState) (w : auth.AuthSess) (hv : viewAt (auth.BkView.uni st) (authD bs.S))
    (hl : hs.getLast? = some st) :
    realInv (GF := GF) γ d s0 q0 ∗ bkTok γ (1 : Qp).half (csT (fun n => bktOf bs.S n)) ∗
      auth.authLockQ γ.γa hs ∗ rbOwnInR d.γB (fun n => n ∈ authBktL) (rbData d.P bs.S) ∗ bkSw γ 1 w ∗
      bOpen d.γB q0 ⊢ |={⊤}=> auth.authWTok γ.γc := by
  iintro ⟨#Hinv, Hx, Hlq, Hro, Hsw, Hq⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq', HT, >Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, >Hbt⟩)
  rotate_left
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ _ y $$ [$Hx $Hbt]
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ _ y $$ [$Hx $Hbt]
  icases Hb with (Hid | Hbb)
  · iunfold bkIdle at Hid
    icases Hid with ⟨%hs', %rc, %w', -, -, >Hbt, -, -, -⟩
    iexfalso; iapply bkTok_half_one γ _ _ $$ [$Hx $Hbt]
  iunfold bkBatch at Hbb
  icases Hbb with ⟨>HT, >Hbt⟩
  iunfold bkTok at Hx Hbt
  icombine Hx Hbt gives %Hxe
  obtain ⟨-, Hxe⟩ := Hxe
  have ha : cs go!"auth" = bktOf bs.S go!"auth" := (congrArg (fun t => t.1) Hxe).symm
  have hu : cs go!"authUsers" = bktOf bs.S go!"authUsers" := (congrArg (fun t => t.2.1) Hxe).symm
  have hr : cs go!"authRoles" = bktOf bs.S go!"authRoles" := (congrArg (fun t => t.2.2) Hxe).symm
  iunfold bkCommon at Hc
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >%Hv⟩
  icases lockQ_rec γ.γa hs st hl $$ Hlq with ⟨Hlq, #HsL⟩
  icases lockQ_idx γ.γa hs ju su $$ [$Hlq $Hsu] with ⟨Hlq, %Hju⟩
  ihave Hbt := (ghostVar_split_half γ.γk 1 (csT cs)).2 $$ [Hx Hbt]
  · rw [← Hxe]; iframe Hx Hbt
  imod Hclose $$ [Ha Hu Hr' Hs Hr Hp Hbt Hlq Hro Hsw Hq] with -
  · inext
    iunfold realSt
    iexists cs, st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr']
    · iunfold bkCommon
      iframe Ha Hu Hr'
      iframe #
      ipureintro
      obtain ⟨-, -, -, hpu, -⟩ := Hv
      exact ⟨viewAt_writer hv ha hu hr, Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
    ileft
    iframe Hs Hr Hp
    ileft
    iunfold bkIdle
    iexists hs, rbData d.P bs.S, w
    iframe Hlq Hro Hsw Hq
    iunfold bkTok
    iframe Hbt
    ipureintro
    refine ⟨hl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro n hn
    rw [bktOf_rbData _ _ _ (rb_auth d n hn)]
    simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ha.symm
    · exact hu.symm
    · exact hr.symm
  imodintro
  iexact HT

theorem rbData_ins_ne (P : BParams) (S : Data) (n m : GoString) (b : BktData) (h : n ≠ m) :
    (rbData P (S.insert n b)).lookup m = (rbData P S).lookup m := by
  rw [rbData_lookup, rbData_lookup, GMap.lookup_insert_ne _ _ h]

theorem encW_sess {w w' : auth.AuthSess} (h : (encW w.users, encW w.roles) = (encW w'.users, encW w'.roles)) :
    w = w' := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  cases w; cases w'
  simp only at h1 h2
  obtain rfl := encW_inj h1
  obtain rfl := encW_inj h2
  rfl

theorem rbPut_true (γB : BNames) (P : BParams) (n : GoString) (S : Data) :
    rbPut (GF := GF) γB P n S true ⊣⊢ iprop(⌜P.RB n = true⌝ ∗ rbPartR γB (fun m => m = n) (rbData P S)) := by
  unfold rbPut rbPutR; simp only [↓reduceIte]; exact .rfl

/-- A claimed part of the auth buckets, as one bucket's and the others'. -/
theorem rbPartR_pick (γB : BNames) (n : GoString) (hn : n ∈ authBktL) (r : GMap GoString BktData) :
    rbPartR (GF := GF) γB (fun m => m ∈ authBktL) r ⊣⊢
      iprop(rbPartR γB (fun m => m = n) r ∗ rbPartR γB (fun m => m ∈ authBktL ∧ m ≠ n) r) := by
  refine (rbPartR_set γB (fun m => m ∈ authBktL) (fun m => m = n ∨ (m ∈ authBktL ∧ m ≠ n)) r ?_).trans
    (rbPartR_split γB _ _ r (fun m h1 h2 => h2.2 h1))
  intro m
  constructor
  · intro h; by_cases e : m = n
    · exact Or.inl e
    · exact Or.inr ⟨h, e⟩
  · rintro (rfl | ⟨h, -⟩)
    · exact hn
    · exact h

/-- **The lock token's resources** besides the batch lock, in the session `bs` at the state `st`, with `X` given
back at `Unlock`: the claimed part of the auth buckets at the writer's contents, half the batch token, half the
session token, the rest of the open share, the backend lock's resources `W` and the hooks' `Pk`, the hook's share
`Hk` (the boot contract's), `X`, the receipts and the facts. -/
def lkR (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (bs : BSess) (st : auth.AuthState)
    (X : IProp GF) : IProp GF :=
  iprop(∃ (x : BktData × BktData × BktData) (w : auth.AuthSess) (k : Nat),
    rbPartR d.γB (fun n => n ∈ authBktL) (rbData d.P bs.S) ∗ bkTok γ (1 : Qp).half x ∗
    bkSw γ (1 : Qp).half w ∗ bOpen d.γB q0 ∗ W ∗ Pk ∗ Hk ∗ X ∗ ⧗ k ∗ ⌜LkOk d bs st x w k⌝)

/-- **The lock token** `Lk st X` of the write contract. -/
def lkT (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (st : auth.AuthState) (X : IProp GF) :
    IProp GF :=
  iprop(∃ bs : BSess, batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)

/-- The receipts after one more write bound the session's pending writes below the backend's room. -/
theorem lk_receipt (hRB : receiptBound GF ≤ 2 ^ 48) (d : mvcc.KBReal) (hPw : d.P.Wf) (bs : BSess)
    (st : auth.AuthState) (x : BktData × BktData × BktData) (w : auth.AuthSess) (k : Nat)
    (hok : LkOk d bs st x w k) :
    (⧗ k : IProp GF) ∗ ⧗ 1 ⊢ |={⊤}=> ⧗ (k + 1) ∗ ⌜sint.Z bs.pend + 1 < 2 ^ 58⌝ := by
  iintro ⟨Hk, H1⟩
  ihave Hk := (receipt_add k 1).2 $$ [$Hk $H1]
  imod receipt_snapshot (k + 1) $$ Hk with ⟨Hk, #Hp⟩
  ihave %Hlt := preceipt_lt (k + 1) $$ Hp
  imodintro
  iframe Hk
  ipureintro
  have h1 := hok.pend
  have h2 := hPw.2.2.1
  omega

/-- **A claimed put into an auth bucket** under the lock token: `UnsafePut` with the bucket's claimed part, the
facts moved by `hstep`, a receipt spent. -/
theorem lk_put (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) (hPw : d.P.Wf)
    (bi : BucketInfo) (hbi : bi.name ∈ authBktL) (hhas : d.P.has bi) (kb vb : GoString)
    (hk0 : 0 < kb.length) (hk1 : kb.length ≤ maxKeySize)
    (st st' : auth.AuthState) (X : IProp GF) (w w' : auth.AuthSess)
    (hstep : ∀ bs x k, LkOk d bs st x w k → sint.Z bs.pend + 1 < 2 ^ 58 →
      LkOk d (bs.put bi kb vb false true) st' x w' (k + 1)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ⊢
      ∀ (bk : GoInterface) (key val : GoSlice),
        {{ isBucket bk bi ∗ key ↦*□ kb ∗ val ↦*□ vb ∗ lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗
            bkSw γ (1 : Qp).half w }}
          (App (App (App (Val #(methods (btIface t).ty go!"UnsafePut" (btIface t).v)) (Val #bk)) (Val #key))
            (Val #val))
        {{ RET #(); lkT γ d q0 W Pk Hk st' X ∗ bkSw γ (1 : Qp).half w' }} := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ %bk %key %val !> %Φ ⟨#Hbk, #Hkey, #Hval, Hlk, Hr1, Hsw⟩ HΦ
  iunfold lkT at Hlk
  icases Hlk with ⟨%bs, Hl, HR⟩
  iunfold lkR at HR
  icases HR with ⟨%x, %w0, %k, Hrp, Hx, Hsw0, Hq, HW, HPk, HHk, HX, Hrk, %Hok⟩
  iunfold bkSw at Hsw Hsw0
  icombine Hsw Hsw0 gives %Hwe
  have hww : w = w0 := encW_sess Hwe.2
  subst hww
  imod ghostVar_update_halves (encW w'.users, encW w'.roles) γ.γw _ _ $$ Hsw Hsw0 with ⟨Hsw, Hsw0⟩
  imod lk_receipt hRB d hPw bs st x w k Hok $$ [$Hrk $Hr1] with ⟨Hrk, %hpend⟩
  icases (rbPartR_pick d.γB bi.name hbi _).1 $$ Hrp with ⟨Hn, Hrest⟩
  ihave Hrbp := (rbPut_true d.γB d.P bi.name bs.S).2 $$ [Hn]
  · iframe Hn; ipureintro; exact rb_auth d _ hbi
  ihave Hhk := hkPut_of_not_HK (hG := hG) d.γB d.P bi.name kb bs.S (hk_auth d _ kb hbi)
  ihave Hfk := fkPut_other (hG := hG) d.γB bi.name kb (fk_auth _ kb hbi)
  wp_apply (@hUP d.γB d.P W Pk d.be t bs bk bi key val kb vb hhas hk0 hk1 hpend
      (fun h => absurd h (by rw [sb_auth d _ hbi]; decide)) (fun h => absurd h (fk_auth _ kb hbi))
      true true (by decide))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hval $Hhk $Hrbp $Hfk] as ⟨Hl, -, Hrbp, -⟩
  have hS : (bs.put bi kb vb false true).S = bs.S.insert bi.name ((bktOf bs.S bi.name).insert kb vb) := rfl
  icases (rbPut_true d.γB d.P bi.name _).1 $$ Hrbp with ⟨-, Hn⟩
  ihave Hrest := rbPartR_congr d.γB _ (rbData d.P bs.S)
    (rbData d.P (bs.S.insert bi.name ((bktOf bs.S bi.name).insert kb vb)))
    (fun m hm => (rbData_ins_ne d.P bs.S bi.name m _ (fun e => hm.2 e.symm)).symm) $$ Hrest
  ihave Hrp := (rbPartR_pick d.γB bi.name hbi _).2 $$ [$Hn $Hrest]
  iapply HΦ
  iunfold bkSw
  iframe Hsw
  iunfold lkT
  iexists bs.put bi kb vb false true
  iframe Hl
  iunfold lkR
  iexists x, w', k + 1
  rw [hS]
  iframe Hrp Hx Hq HW HPk HHk HX Hrk
  iunfold bkSw
  iframe Hsw0
  ipureintro; exact hstep bs x k Hok hpend

/-- **A claimed put into the `auth` bucket** (as `lk_put`, the session's writes unchanged: no session token). -/
theorem lk_putA (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) (hPw : d.P.Wf)
    (bi : BucketInfo) (hbi : bi.name ∈ authBktL) (hhas : d.P.has bi) (kb vb : GoString)
    (hk0 : 0 < kb.length) (hk1 : kb.length ≤ maxKeySize)
    (st st' : auth.AuthState) (X : IProp GF)
    (hstep : ∀ bs x w k, LkOk d bs st x w k → sint.Z bs.pend + 1 < 2 ^ 58 →
      LkOk d (bs.put bi kb vb false true) st' x w (k + 1)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ⊢
      ∀ (bk : GoInterface) (key val : GoSlice),
        {{ isBucket bk bi ∗ key ↦*□ kb ∗ val ↦*□ vb ∗ lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 }}
          (App (App (App (Val #(methods (btIface t).ty go!"UnsafePut" (btIface t).v)) (Val #bk)) (Val #key))
            (Val #val))
        {{ RET #(); lkT γ d q0 W Pk Hk st' X }} := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ %bk %key %val !> %Φ ⟨#Hbk, #Hkey, #Hval, Hlk, Hr1⟩ HΦ
  iunfold lkT at Hlk
  icases Hlk with ⟨%bs, Hl, HR⟩
  iunfold lkR at HR
  icases HR with ⟨%x, %w0, %k, Hrp, Hx, Hsw0, Hq, HW, HPk, HHk, HX, Hrk, %Hok⟩
  imod lk_receipt hRB d hPw bs st x w0 k Hok $$ [$Hrk $Hr1] with ⟨Hrk, %hpend⟩
  icases (rbPartR_pick d.γB bi.name hbi _).1 $$ Hrp with ⟨Hn, Hrest⟩
  ihave Hrbp := (rbPut_true d.γB d.P bi.name bs.S).2 $$ [Hn]
  · iframe Hn; ipureintro; exact rb_auth d _ hbi
  ihave Hhk := hkPut_of_not_HK (hG := hG) d.γB d.P bi.name kb bs.S (hk_auth d _ kb hbi)
  ihave Hfk := fkPut_other (hG := hG) d.γB bi.name kb (fk_auth _ kb hbi)
  wp_apply (@hUP d.γB d.P W Pk d.be t bs bk bi key val kb vb hhas hk0 hk1 hpend
      (fun h => absurd h (by rw [sb_auth d _ hbi]; decide)) (fun h => absurd h (fk_auth _ kb hbi))
      true true (by decide))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hval $Hhk $Hrbp $Hfk] as ⟨Hl, -, Hrbp, -⟩
  have hS : (bs.put bi kb vb false true).S = bs.S.insert bi.name ((bktOf bs.S bi.name).insert kb vb) := rfl
  icases (rbPut_true d.γB d.P bi.name _).1 $$ Hrbp with ⟨-, Hn⟩
  ihave Hrest := rbPartR_congr d.γB _ (rbData d.P bs.S)
    (rbData d.P (bs.S.insert bi.name ((bktOf bs.S bi.name).insert kb vb)))
    (fun m hm => (rbData_ins_ne d.P bs.S bi.name m _ (fun e => hm.2 e.symm)).symm) $$ Hrest
  ihave Hrp := (rbPartR_pick d.γB bi.name hbi _).2 $$ [$Hn $Hrest]
  iapply HΦ
  iunfold lkT
  iexists bs.put bi kb vb false true
  iframe Hl
  iunfold lkR
  iexists x, w0, k + 1
  rw [hS]
  iframe Hrp Hx Hsw0 Hq HW HPk HHk HX Hrk
  ipureintro; exact hstep bs x w0 k Hok hpend

/-- **A claimed delete from an auth bucket** under the lock token (as `lk_put`). -/
theorem lk_del (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) (hPw : d.P.Wf)
    (bi : BucketInfo) (hbi : bi.name ∈ authBktL) (hhas : d.P.has bi) (kb : GoString)
    (st st' : auth.AuthState) (X : IProp GF) (w w' : auth.AuthSess)
    (hstep : ∀ bs x k, LkOk d bs st x w k → sint.Z bs.pend + 1 < 2 ^ 58 →
      LkOk d (bs.del bi kb true) st' x w' (k + 1)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ⊢
      ∀ (bk : GoInterface) (key : GoSlice),
        {{ isBucket bk bi ∗ key ↦* kb ∗ lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗ bkSw γ (1 : Qp).half w }}
          (App (App (Val #(methods (btIface t).ty go!"UnsafeDelete" (btIface t).v)) (Val #bk)) (Val #key))
        {{ RET #(); lkT γ d q0 W Pk Hk st' X ∗ bkSw γ (1 : Qp).half w' }} := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ %bk %key !> %Φ ⟨#Hbk, Hkey, Hlk, Hr1, Hsw⟩ HΦ
  iunfold lkT at Hlk
  icases Hlk with ⟨%bs, Hl, HR⟩
  iunfold lkR at HR
  icases HR with ⟨%x, %w0, %k, Hrp, Hx, Hsw0, Hq, HW, HPk, HHk, HX, Hrk, %Hok⟩
  iunfold bkSw at Hsw Hsw0
  icombine Hsw Hsw0 gives %Hwe
  have hww : w = w0 := encW_sess Hwe.2
  subst hww
  imod ghostVar_update_halves (encW w'.users, encW w'.roles) γ.γw _ _ $$ Hsw Hsw0 with ⟨Hsw, Hsw0⟩
  imod lk_receipt hRB d hPw bs st x w k Hok $$ [$Hrk $Hr1] with ⟨Hrk, %hpend⟩
  icases (rbPartR_pick d.γB bi.name hbi _).1 $$ Hrp with ⟨Hn, Hrest⟩
  ihave Hrbp := (rbPut_true d.γB d.P bi.name bs.S).2 $$ [Hn]
  · iframe Hn; ipureintro; exact rb_auth d _ hbi
  ihave Hdl := dlPut_other (hG := hG) d.γB d.P bi.name (sb_auth d _ hbi)
  ihave Hkey : (if true then key ↦*{DFrac.own 1} kb else txBytes bs.tx d.γB.db key kb : IProp GF) $$ [Hkey]
  · simp only [↓reduceIte]; iexact Hkey
  wp_apply (@hDel d.γB d.P W Pk d.be t bs bk bi key kb (DFrac.own 1) true hhas hpend
      (hkb_auth d _ kb hbi) (fk_auth _ kb hbi) (fun h => absurd h (by rw [sb_auth d _ hbi]; decide))
      true true (by decide))
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hrbp $Hdl] as ⟨Hl, -, Hrbp, -⟩
  have hS : (bs.del bi kb true).S = bs.S.insert bi.name ((bktOf bs.S bi.name).delete kb) := rfl
  icases (rbPut_true d.γB d.P bi.name _).1 $$ Hrbp with ⟨-, Hn⟩
  ihave Hrest := rbPartR_congr d.γB _ (rbData d.P bs.S)
    (rbData d.P (bs.S.insert bi.name ((bktOf bs.S bi.name).delete kb)))
    (fun m hm => (rbData_ins_ne d.P bs.S bi.name m _ (fun e => hm.2 e.symm)).symm) $$ Hrest
  ihave Hrp := (rbPartR_pick d.γB bi.name hbi _).2 $$ [$Hn $Hrest]
  iapply HΦ
  iunfold bkSw
  iframe Hsw
  iunfold lkT
  iexists bs.del bi kb true
  iframe Hl
  iunfold lkR
  iexists x, w', k + 1
  rw [hS]
  iframe Hrp Hx Hq HW HPk HHk HX Hrk
  iunfold bkSw
  iframe Hsw0
  ipureintro; exact hstep bs x k Hok hpend

/-- **The claim after the batch lock is taken** (`lk_lock`'s and `lk_lockOut`'s continuation): from a free session `bs`
and what `real_borrow` lent, the lock token's parts at the borrowed state, with `X`; the session's pending writes below
the backend's limit. -/
theorem lk_claim (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk X : IProp GF) (cs : GoString → BktData)
    (hs : List auth.AuthState) (rc : GMap GoString BktData) (w : auth.AuthSess) (st : auth.AuthState)
    (Hbr : hs.getLast? = some st ∧ viewAt ⟨st, st, st⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ ∧
      ∀ n, n ∈ authBktL → bktOf rc n = cs n)
    (bs : BSess) (Hfree : freeOk d.P bs) :
    batchLocked (GF := GF) d.γB d.P d.be bs ∗ W ∗ Pk ∗ X ∗ bOpen d.γB q0 ∗ Hk ∗
      auth.authLockQ γ.γa hs ∗ rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗ bkTok γ (1 : Qp).half (csT cs) ∗
      bkSw γ 1 w ⊢ |={⊤}=> ∃ (st : auth.AuthState) (bs' : BSess), ⌜sint.Z bs'.pend < sint.Z d.P.limit⌝ ∗
        batchLocked d.γB d.P d.be bs' true ∗ lkR γ d q0 W Pk Hk bs' st X ∗
        bkSw γ (1 : Qp).half auth.AuthSess.init ∗ auth.authLockI (.on γ.γa) st := by
  iintro ⟨Hl, HW, HPk, HPost, Hq, HHk, Hlq, Hro, Hbt, Hsw⟩
  icases batchLocked_cwOk d.γB d.P d.be bs false $$ Hl with ⟨Hl, %Hcw⟩
  ihave Hl := batchLocked_claimed d.γB d.P d.be bs $$ Hl
  ihave Hrp := rbOwnInR_part d.γB _ rc $$ Hro
  imod batchLocked_rbPartR_agree d.γB d.P d.be bs true _ rc go!"auth" (by simp [authBktL]) ⊤
    CoPset.subseteq_top $$ [$Hl $Hrp] with ⟨Hl, Hrp, %ha⟩
  imod batchLocked_rbPartR_agree d.γB d.P d.be bs true _ rc go!"authUsers" (by simp [authBktL]) ⊤
    CoPset.subseteq_top $$ [$Hl $Hrp] with ⟨Hl, Hrp, %hu⟩
  imod batchLocked_rbPartR_agree d.γB d.P d.be bs true _ rc go!"authRoles" (by simp [authBktL]) ⊤
    CoPset.subseteq_top $$ [$Hl $Hrp] with ⟨Hl, Hrp, %hr⟩
  have hlk : ∀ n, n ∈ authBktL → rc.lookup n = (rbData d.P bs.S).lookup n := by
    intro n hn
    simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ha
    · exact hu
    · exact hr
  ihave Hrp := rbPartR_congr d.γB _ rc (rbData d.P bs.S) hlk $$ Hrp
  have hcs : ∀ n, n ∈ authBktL → bktOf bs.S n = cs n := by
    intro n hn
    rw [← bktOf_rbData d.P bs.S n (rb_auth d n hn), ← Hbr.2.2 n hn]
    unfold bktOf; rw [hlk n hn]
  imod receipt_zero (GF := GF) with Hr0
  iunfold bkSw at Hsw
  imod ghostVar_update (encW auth.AuthSess.init.users, encW auth.AuthSess.init.roles) $$ Hsw with Hsw
  icases (ghostVar_split_half γ.γw 1 _).1 $$ Hsw with ⟨Hs1, Hs2⟩
  imodintro
  iexists st, bs
  isplitr
  · ipureintro; exact Hfree.2.1
  isplitl [Hl]
  · iexact Hl
  isplitl [Hrp Hbt Hs1 Hq HW HPk HHk HPost Hr0]
  · iunfold lkR
    iexists csT cs, auth.AuthSess.init, 0
    iframe Hrp Hbt Hq HW HPk HHk HPost Hr0
    iunfold bkSw
    iframe Hs1
    ipureintro
    have hidle : ∀ n, n ∈ authBktL → bs.tk n = .idle := fun n hn => Hfree.2.2.2.2.2 n (rb_auth d n hn)
    have hca := hcs go!"auth" (by simp [authBktL])
    have hcu := hcs go!"authUsers" (by simp [authBktL])
    have hcr := hcs go!"authRoles" (by simp [authBktL])
    exact {
      hw := Hfree.2.2.2.2.1
      vs := ⟨vData_free d.P bs Hfree.1 Hfree.2.2.1 Hfree.2.2.2.1, Hfree.2.2.2.1⟩
      cw := fun n hn => by rw [Hcw rfl Hfree.2.2.2.2.1 n] at hn; cases hn
      pend := by have := Hfree.2.1; push_cast; omega
      ka := Or.inl (hidle _ (by simp [authBktL]))
      ku := by rw [hidle _ (by simp [authBktL])]; rfl
      kr := by rw [hidle _ (by simp [authBktL])]; rfl
      ia := fun _ => hca
      iu := fun _ => hcu
      ir := fun _ => hcr
      view := by
        rw [authD_eq, hca, hcu, hcr]
        exact Hbr.2.1 }
  iunfold bkSw
  iframe Hs2
  simp only [auth.authLockI, auth.authLockShare, auth.histLast]
  iexists hs
  iframe Hlq
  ipureintro; exact Hbr.1

/-- **`Lock()`** (`LockInsideApply` under the critical-section contract at the hook `f` with the hooks' resource
`Pk`, the write token and the hook's share `Hk`): the write token deposited in the invariant (the batch branch), the
hook run, the batch lock taken in the claimed mode with the claimed part of the auth buckets (idle, at the writer's
contents: the agreement law), half the batch token and the session token, the rest of the open share, `W ∗ Pk`, the
contract's `Post`, no receipt; the client gets the lock's share of the history, at the buckets' state. -/
theorem lk_lock (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) (dq : DFrac) (f : GoFunc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ∗ realInv γ d s0 q0 ∗
      □ (Hk -∗ plHookAt d.γB dq f ∗ (plHookAt d.γB dq f -∗ Hk)) ⊢
      ∀ (Pre Q Post : IProp GF),
        {{ srvApi.csContractA Pk f Pre Q Post ∗ auth.authWTok γ.γc ∗ Hk }}
          (App (Val #(methods (btIface t).ty go!"LockInsideApply" (btIface t).v)) (Val #()))
        {{ RET #(); ∃ st : auth.AuthState, lkT γ d q0 W Pk Hk st Post ∗
            bkSw γ (1 : Qp).half auth.AuthSess.init ∗ auth.authLockI (.on γ.γa) st }} := by
  iintro ⟨#Hpkg, #Hb, #Ht, #Hinv, #Hhk⟩ %Pre %Q %Post !> %Φ ⟨Hcs, HT, HHk⟩ HΦ
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨Hpre, Hhr, Hfin⟩
  imod real_borrow γ d s0 q0 $$ [$Hinv $HT] with ⟨%cs, %hs, %rc, %w, %st, Hlq, Hro, Hbt, Hsw, Hq, %Hbr⟩
  icases Hhk $$ HHk with ⟨Hpl, Hplb⟩
  by_cases hf : f = func.nil
  · subst hf
    simp only [mvcc.api.hookRun, ↓reduceIte]
    iapply wp_fupd
    wp_apply (hLI d.γB d.P W Pk d.be t q0 dq func.nil Pre iprop(|={⊤}=> Q))
      $$ [$Hb $Ht $Hq $Hpl $Hpre Hhr] as ⟨%bs, Hl, %Hfree, HW, HQ, Hq, Hpl⟩
    · ileft
      isplitr
      · ipureintro; rfl
      iexact Hhr
    imod HQ with HQ
    imod Hfin $$ HQ with ⟨HPk, HPost⟩
    ihave HHk := Hplb $$ Hpl
    imod lk_claim γ d q0 W Pk Hk Post cs hs rc w st Hbr bs Hfree $$ [$Hl $HW $HPk $HPost $Hq $HHk $Hlq $Hro $Hbt $Hsw]
      with ⟨%st', %bs', -, Hl, HR, Hsw, HI⟩
    imodintro
    iapply HΦ
    iexists st'
    iframe Hsw HI
    iunfold lkT; iexists bs'; iframe Hl HR
  · simp only [mvcc.api.hookRun, hf, ↓reduceIte]
    iapply wp_fupd
    wp_apply (hLI d.γB d.P W Pk d.be t q0 dq f Pre Q)
      $$ [$Hb $Ht $Hq $Hpl $Hpre Hhr] as ⟨%bs, Hl, %Hfree, HW, HQ, Hq, Hpl⟩
    · iright
      isplitr
      · ipureintro; exact hf
      iexact Hhr
    imod Hfin $$ HQ with ⟨HPk, HPost⟩
    ihave HHk := Hplb $$ Hpl
    imod lk_claim γ d q0 W Pk Hk Post cs hs rc w st Hbr bs Hfree $$ [$Hl $HW $HPk $HPost $Hq $HHk $Hlq $Hro $Hbt $Hsw]
      with ⟨%st', %bs', -, Hl, HR, Hsw, HI⟩
    imodintro
    iapply HΦ
    iexists st'
    iframe Hsw HI
    iunfold lkT; iexists bs'; iframe Hl HR

/-- **Between the backend's `Unlock()` and `Commit()`** (schema's `Unlock` makes both calls): `X`, the hook's share,
the rest of the open share and the second write-back token; the batch token at the writer's contents with the lock's
share of the history (`unRr'`, from the confirmation), the claimed part idle, the session token whole. -/
def unC (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (Hk X Y : IProp GF) : IProp GF :=
  iprop(∃ (bs : BSess) (st : auth.AuthState) (hs : List auth.AuthState) (w : auth.AuthSess),
    X ∗ Hk ∗ bOpen d.γB q0 ∗ Y ∗ unRr' γ bs st hs ∗
    rbOwnInR d.γB (fun n => n ∈ authBktL) (rbData d.P bs.S) ∗ bkSw γ 1 w ∗
    ⌜viewAt (auth.BkView.uni st) (authD bs.S)⌝)

/-- **The backend's `Unlock()`** under the lock token, with the session token, the lock's share of the history at the
token's state and two write-back tokens: the claimed part handed in with the windows (`real_acc`) and the
confirmation (`real_conf`) around the invariant; the session changed nothing the readers see (`viewSame`). -/
theorem rbClaimN_authReal : (↑rbClaimN : CoPset) ⊆ ⊤ \ ↑authRealN := by
  unfold authRealN
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "backend" ≠ "authReal") p
    ⟨nclose_subseteq (nroot.@"backend") "rbclaim" p hp, h'⟩⟩

theorem lk_unlock (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ∗ realInv γ d s0 q0 ⊢
      ∀ (st : auth.AuthState) (X : IProp GF) (w : auth.AuthSess) (Y : IProp GF),
        {{ lkT γ d q0 W Pk Hk st X ∗ bkSw γ (1 : Qp).half w ∗ auth.authLockI (.on γ.γa) st ∗
            wbTok d.γB ∗ Y }}
          (App (Val #(methods (btIface t).ty go!"Unlock" (btIface t).v)) (Val #()))
        {{ RET #(); unC γ d q0 Hk X Y }} := by
  iintro ⟨#Hpkg, #Hb, #Ht, #Hinv⟩ %st %X %w %Y !> %Φ ⟨Hlk, Hsw, HI, Hw1, Hw2⟩ HΦ
  icases isBackend_b d.γB d.P W Pk d.be $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -, %HPw⟩
  iunfold lkT at Hlk
  icases Hlk with ⟨%bs, Hl, HR⟩
  iunfold lkR at HR
  icases HR with ⟨%x, %w0, %k, Hrp, Hx, Hsw0, Hq, HW, HPk, HHk, HX, Hrk, %Hok⟩
  iunfold bkSw at Hsw Hsw0
  icombine Hsw Hsw0 gives %Hwe
  have hww : w = w0 := encW_sess Hwe.2
  subst hww
  ihave Hswf : bkSw γ 1 w $$ [Hsw Hsw0]
  · iunfold bkSw; iapply (ghostVar_split_half γ.γw 1 _).2; iframe Hsw Hsw0
  simp only [auth.authLockI, auth.authLockShare, auth.histLast]
  icases HI with ⟨%hs, Hlq, %hl⟩
  imod receipt_snapshot k $$ Hrk with ⟨-, #Hpr⟩
  ihave %Hlt := preceipt_lt k $$ Hpr
  have hroom : sint.Z bs.pend + d.P.hookMax < 2 ^ 58 := by
    have := Hok.pend; have := HPw.2.2.1; have := HPw.2.2.2.1
    omega
  ihave #Hacc := real_acc γ d s0 q0 bs st hs Hok.view $$ Hinv
  ihave Hcf := real_conf γ d s0 q0 bs st hs Hok.view $$ Hinv
  ihave Hrb := rbPart_none (hG := hG) d.γB (∅ : GMap GoString BktData)
  ihave HRr : unRr γ bs st hs $$ [Hx Hlq]
  · iunfold unRr; iexists x; iframe Hx Hlq; ipureintro; exact ⟨hl, Hok.tkOk⟩
  icases viewSame_thin (hG := hG) d.γB d.P bs Hok.vs with ⟨#Hth, %Hwe0⟩
  wp_apply (hUL d.γB d.P W Pk d.be t bs iprop(X ∗ Hk ∗ bOpen d.γB q0 ∗ bkSw γ 1 w) (fun _ => False) ∅ authBktL
      (rbData d.P bs.S) (unRr γ bs st hs) (unRr' γ bs st hs) (⊤ ∖ ↑authRealN) rbClaimN_authReal Hok.hw hroom
      (by decide) Hok.cw)
    $$ [$Hb $Ht $Hl $Hw1 $Hrb $Hrp $HRr $Hacc $Hcf HW HPk HX HHk Hq Hswf] as ⟨⟨HX, HHk, Hq, Hswf⟩, -, Hro, HRr'⟩
  · ileft
    iframe Hth HW HPk HX HHk Hq Hswf
    ipureintro; exact Hwe0
  iapply HΦ
  iunfold unC
  iexists bs, st, hs, w
  iframe HX HHk Hq Hw2 HRr' Hro Hswf
  ipureintro; exact Hok.view

/-- **The backend's `Commit()`** after `Unlock()`: commits (nothing pending), then the batch ends in the invariant
(`real_return`): the buckets idle at the session's state, the write token back. -/
theorem lk_commit (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) (t : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ∗ realInv γ d s0 q0 ⊢
      ∀ X : IProp GF,
        {{ unC γ d q0 Hk X (wbTok d.γB) }}
          (App (Val #(methods (btIface t).ty go!"Commit" (btIface t).v)) (Val #()))
        {{ RET #(); X ∗ auth.authWTok γ.γc ∗ Hk }} := by
  iintro ⟨#Hpkg, #Hb, #Ht, #Hinv⟩ %X !> %Φ HC HΦ
  iunfold unC at HC
  icases HC with ⟨%bs, %st, %hs, %w, HX, HHk, Hq, Hw, HRr', Hro, Hsw, %Hv⟩
  iunfold unRr' at HRr'
  icases HRr' with ⟨Hx, Hlq, %hl⟩
  iapply wp_fupd
  wp_apply (hCm d.γB d.P W Pk d.be t q0 iprop(True) iprop(True)) $$ [$Hb $Ht $Hq $Hw] as ⟨Hq, -⟩
  · isplitr
    · itrivial
    iapply commitReq_true
  imod real_return γ d s0 q0 bs st hs w Hv hl $$ [$Hinv $Hx $Hlq $Hro $Hsw $Hq] with HT
  imodintro
  iapply HΦ
  iframe HX HT HHk

section iface
variable [GooseExts] [GoGlobalContext]

/-- A schema auth batch transaction `l` as an interface. -/
abbrev abtIface (l : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBatchTx.ty, #l⟩

end iface

theorem lkR_view (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (bs : BSess)
    (st : auth.AuthState) (X : IProp GF) :
    lkR γ d q0 W Pk Hk bs st X ⊢ lkR γ d q0 W Pk Hk bs st X ∗ ⌜viewAt (auth.BkView.uni st) (authD bs.S)⌝ := by
  iunfold lkR
  iintro ⟨%x, %w, %k, H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hok⟩
  isplitl
  · iexists x, w, k; iframe; ipureintro; exact Hok
  · ipureintro; exact Hok.view

/-- **The batch transaction's reads under the lock token** (the write contract's reader and its two `X` reads). -/
theorem lk_reads (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk : IProp GF) (l t lg : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ∗
      schema.abtF go!"tx" l ↦□ (GoInterface.ok (btIface t) : GoInterface) ∗ schema.abtF go!"lg" l ↦□ lg ⊢
      (□ ∀ X : IProp GF, auth.authReaderOk (abtIface l) (fun st => lkT γ d q0 W Pk Hk st X)) ∗
      □ (∀ (st : auth.AuthState) (X : IProp GF) (name : GoString),
        {{ lkT γ d q0 W Pk Hk st X }} (App (Val #(methods (abtIface l).ty go!"UnsafeGetUser" (abtIface l).v)) (Val #name))
        {{ (u : Loc), RET #u; lkT γ d q0 W Pk Hk st X ∗ auth.userOutX u st name }}) ∗
      □ (∀ (st : auth.AuthState) (X : IProp GF) (name : GoString),
        {{ lkT γ d q0 W Pk Hk st X }} (App (Val #(methods (abtIface l).ty go!"UnsafeGetRole" (abtIface l).v)) (Val #name))
        {{ (r : Loc), RET #r; lkT γ d q0 W Pk Hk st X ∗ auth.roleOutX r st name }}) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Ht, #Htx, #Hlg⟩
  isplitr
  · iintro !> %X
    iunfold auth.authReaderOk
    isplitr
    · iintro !> %st %name !> %Φ Hlk HΦ
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl, HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
      ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
        (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
      simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
      obtain ⟨-, ⟨dU, hu⟩, -⟩ := Hv
      iapply wp_fupd
      wp_apply (hGU l (btIface t) lg name (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) dU (schema.usersAt_dec hu))
        $$ [$Hp2 $Htx $Hlg $Hrd Hl HR] as %u ⟨⟨Hl, HR⟩, Hu⟩
      · iframe Hl HR
      imod schema.userOutDX_persist u _ name dU $$ Hu with Hu
      imodintro
      iapply HΦ
      isplitl [Hl HR]
      · iunfold lkT; iexists bs; iframe Hl HR
      iapply schema.userOutD_are st _ u name dU hu $$ Hu
    isplitr
    · iintro !> %st %name !> %Φ Hlk HΦ
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl, HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
      ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
        (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
      simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
      obtain ⟨-, -, ⟨dR, hr⟩⟩ := Hv
      iapply wp_fupd
      wp_apply (hGR l (btIface t) lg name (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) dR (schema.rolesAt_dec hr))
        $$ [$Hp2 $Htx $Hlg $Hrd Hl HR] as %u ⟨⟨Hl, HR⟩, Hu⟩
      · iframe Hl HR
      imod schema.roleOutDX_persist ⊤ u _ name dR $$ Hu with Hu
      imodintro
      iapply HΦ
      isplitl [Hl HR]
      · iunfold lkT; iexists bs; iframe Hl HR
      iapply schema.roleOutD_are st _ u name dR hr $$ Hu
    isplitr
    · iintro !> %st !> %Φ Hlk HΦ
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl, HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
      ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
        (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
      wp_apply (hEn l (btIface t) (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S)) $$ [$Hp2 $Htx $Hrd Hl HR] as %b ⟨⟨Hl, HR⟩, %Hb'⟩
      · iframe Hl HR
      iapply HΦ
      isplitl [Hl HR]
      · iunfold lkT; iexists bs; iframe Hl HR
      ipureintro
      rw [Hb', enabledOf_auth]; exact Hv.1.1
    isplitr
    · iintro !> %st !> %Φ Hlk HΦ
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl, HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
      ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
        (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
      wp_apply (hRev l (btIface t) (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) Hv.1.2.2) $$ [$Hp2 $Htx $Hrd Hl HR] as %r ⟨⟨Hl, HR⟩, %Hr⟩
      · iframe Hl HR
      iapply HΦ
      isplitl [Hl HR]
      · iunfold lkT; iexists bs; iframe Hl HR
      ipureintro
      rw [Hr, revisionOf_auth]; exact Hv.1.2.1
    · iintro !> %st !> %Φ Hlk HΦ
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl, HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
      ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
        (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
      simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
      obtain ⟨-, ⟨dU, hu⟩, -⟩ := Hv
      wp_apply (hGA l (btIface t) lg (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) dU (schema.usersAt_dec hu))
        $$ [$Hp2 $Htx $Hlg $Hrd Hl HR] as %s ⟨⟨Hl, HR⟩, Hs⟩
      · iframe Hl HR
      ihave Hs := usersOutD_at st _ dU s hu $$ Hs
      iunfold auth.usersOut at Hs
      icases Hs with ⟨%us, %names, Hs, %Hn, Hl'⟩
      iapply HΦ
      iframe Hs Hl'
      isplitl [Hl HR]
      · iunfold lkT; iexists bs; iframe Hl HR
      ipureintro; exact Hn
  isplitr
  · iintro !> %st %X %name !> %Φ Hlk HΦ
    iunfold lkT at Hlk
    icases Hlk with ⟨%bs, Hl, HR⟩
    icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
    ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
      (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
    simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
    obtain ⟨-, ⟨dU, hu⟩, -⟩ := Hv
    wp_apply (hGU l (btIface t) lg name (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) dU (schema.usersAt_dec hu))
      $$ [$Hp2 $Htx $Hlg $Hrd Hl HR] as %u ⟨⟨Hl, HR⟩, Hu⟩
    · iframe Hl HR
    iapply HΦ
    isplitl [Hl HR]
    · iunfold lkT; iexists bs; iframe Hl HR
    iapply schema.userOutDX_are st _ u name dU hu $$ Hu
  · iintro !> %st %X %name !> %Φ Hlk HΦ
    iunfold lkT at Hlk
    icases Hlk with ⟨%bs, Hl, HR⟩
    icases lkR_view γ d q0 W Pk Hk bs st X $$ HR with ⟨HR, %Hv⟩
    ihave #Hrd := bt_reader hUR hFE hID hName hSafe d.γB d.P W Pk d.be t bs true
      (lkR γ d q0 W Pk Hk bs st X) $$ [$Hp1 $Hp2 $Hb $Ht]
    simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
    obtain ⟨-, -, ⟨dR, hr⟩⟩ := Hv
    wp_apply (hGR l (btIface t) lg name (iprop(batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X)) (authD bs.S) dR (schema.rolesAt_dec hr))
      $$ [$Hp2 $Htx $Hlg $Hrd Hl HR] as %u ⟨⟨Hl, HR⟩, Hu⟩
    · iframe Hl HR
    iapply HΦ
    isplitl [Hl HR]
    · iunfold lkT; iexists bs; iframe Hl HR
    iapply schema.roleOutDX_are st _ u name dR hr $$ Hu

/-- **Schema's batch transaction over the real backend meets the store's write contract** (`auth.authBatchTxLkR` in
`on γa`, at the hook `f` with the hooks' resource `Pk`, the write token `T = authWTok ∗ Hk` and the write-back token):
the lock token `lkT`, the session token half `bkSw`. -/
theorem real_batchTxLkR
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) (hPw : d.P.Wf) (hP : schema.authHas d.P)
    (l t lg : Loc) (dq : DFrac) (f : GoFunc) (T : IProp GF)
    (hT : T ⊣⊢ iprop(auth.authWTok γ.γc ∗ Hk)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ∗ realInv γ d s0 q0 ∗
      schema.abtF go!"tx" l ↦□ (GoInterface.ok (btIface t) : GoInterface) ∗ schema.abtF go!"lg" l ↦□ lg ∗
      □ (Hk -∗ plHookAt d.γB dq f ∗ (plHookAt d.γB dq f -∗ Hk)) ⊢
      auth.authBatchTxLkR (abtIface l) (.on γ.γa) Pk f T (wbTok d.γB)
        (lkT γ d q0 W Pk Hk) (fun w => bkSw γ (1 : Qp).half w) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Ht, #Hinv, #Htx, #Hlg, #Hhk⟩
  ihave ⟨#Hrd, #HGUX, #HGRX⟩ := lk_reads hUR hFE hID hName hSafe hGU hGR hEn hRev hGA γ d q0 W Pk Hk l t lg
    $$ [$Hp1 $Hp2 $Hb $Ht $Htx $Hlg]
  ihave #Hlock := lk_lock hLI γ d s0 q0 W Pk Hk t dq f $$ [$Hp1 $Hb $Ht $Hinv $Hhk]
  ihave #Hunl := lk_unlock hUL hRB γ d s0 q0 W Pk Hk t $$ [$Hp1 $Hb $Ht $Hinv]
  ihave #Hcom := lk_commit hCm γ d s0 q0 W Pk Hk t $$ [$Hp1 $Hb $Ht $Hinv]
  iunfold auth.authBatchTxLkR
  -- Lock
  isplitr
  · iintro !> %Pre %Q %Post !> %Φ ⟨Hcs, HT⟩ HΦ
    icases hT.1 $$ HT with ⟨HT, HHk⟩
    wp_apply (hLk l (btIface t) iprop(srvApi.csContractA Pk f Pre Q Post ∗ auth.authWTok γ.γc ∗ Hk) _)
      $$ [$Hp2 $Htx Hcs HT HHk] as H
    · iframe Hcs HT HHk
      iapply Hlock
    iapply HΦ
    iexact H
  isplitr
  · iexact Hrd
  -- UnsafePutUser
  isplitr
  · iintro !> %st %X %u %ur %w !> %Φ ⟨Hlk, Hr1, Hsw, Hown, %Hc⟩ HΦ
    obtain ⟨hw, hs, hk0, hk1, hutf⟩ := Hc
    wp_apply (hPU l (btIface t) lg u ur iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗ bkSw γ (1 : Qp).half w)
        iprop(lkT γ d q0 W Pk Hk (auth.putUserRec st ur) X ∗
          bkSw γ (1 : Qp).half { w with users := .puts }) hutf)
      $$ [$Hp2 $Htx $Hlg $Hown Hlk Hr1 Hsw] as ⟨Hown, Hlk, Hsw⟩
    · iframe Hlk Hr1 Hsw
      iintro !> %bk %key %val !> %Ψ ⟨#Hg, #Hkey, #Hval, Hlk, Hr1, Hsw⟩ HΨ
      ihave #Hbk := schema.authUsers_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_put hUP hRB γ d q0 W Pk Hk t hPw mvcc.authUsersBI (by simp [authBktL, authUsersBI_name]) hP.2.1
        ur.name (auth.userEncode ur) hk0 hk1 st (auth.putUserRec st ur) X w { w with users := .puts }
        (fun bs x k h hb => lkOk_putUser hPw hP.2.1 ur h hb hw hs)) $$ [$Hp1 $Hb $Ht] %bk %key %val %Ψ
        [$Hbk $Hkey $Hval $Hlk $Hr1 $Hsw] HΨ
    iapply HΦ
    iframe Hown Hlk Hsw
  -- UnsafeDeleteUser
  isplitr
  · iintro !> %st %X %name %w !> %Φ ⟨Hlk, Hr1, Hsw, %Hc⟩ HΦ
    wp_apply (hDU l (btIface t) name iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗ bkSw γ (1 : Qp).half w)
        iprop(lkT γ d q0 W Pk Hk (auth.delUser st name) X ∗ bkSw γ (1 : Qp).half { w with users := .dels }))
      $$ [$Hp2 $Htx Hlk Hr1 Hsw] as ⟨Hlk, Hsw⟩
    · iframe Hlk Hr1 Hsw
      iintro !> %bk %key !> %Ψ ⟨#Hg, Hkey, Hlk, Hr1, Hsw⟩ HΨ
      ihave #Hbk := schema.authUsers_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_del hDel hRB γ d q0 W Pk Hk t hPw mvcc.authUsersBI (by simp [authBktL, authUsersBI_name]) hP.2.1
        name st (auth.delUser st name) X w { w with users := .dels }
        (fun bs x k h hb => lkOk_delUser name h hb Hc)) $$ [$Hp1 $Hb $Ht] %bk %key %Ψ
        [$Hbk $Hkey $Hlk $Hr1 $Hsw] HΨ
    iapply HΦ
    iframe Hlk Hsw
  -- UnsafePutRole
  isplitr
  · iintro !> %st %X %r %rr %ps %w !> %Φ ⟨Hlk, Hr1, Hsw, Hown, %Hc⟩ HΦ
    obtain ⟨hw, hk0, hk1, hp⟩ := Hc
    wp_apply (hPR l (btIface t) lg r rr iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗ bkSw γ (1 : Qp).half w)
        iprop(lkT γ d q0 W Pk Hk (auth.putRole st rr.name ps) X ∗
          bkSw γ (1 : Qp).half { w with roles := .puts }))
      $$ [$Hp2 $Htx $Hlg $Hown Hlk Hr1 Hsw] as ⟨Hown, Hlk, Hsw⟩
    · iframe Hlk Hr1 Hsw
      iintro !> %bk %key %val !> %Ψ ⟨#Hg, #Hkey, #Hval, Hlk, Hr1, Hsw⟩ HΨ
      ihave #Hbk := schema.authRoles_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_put hUP hRB γ d q0 W Pk Hk t hPw mvcc.authRolesBI (by simp [authBktL, authRolesBI_name]) hP.2.2
        rr.name (auth.roleEncode rr) hk0 hk1 st (auth.putRole st rr.name ps) X w { w with roles := .puts }
        (fun bs x k h hb => lkOk_putRole hPw hP.2.2 rr ps h hb hw hp)) $$ [$Hp1 $Hb $Ht] %bk %key %val %Ψ
        [$Hbk $Hkey $Hval $Hlk $Hr1 $Hsw] HΨ
    iapply HΦ
    iframe Hown Hlk Hsw
  -- UnsafeDeleteRole
  isplitr
  · iintro !> %st %X %name %w !> %Φ ⟨Hlk, Hr1, Hsw, %Hc⟩ HΦ
    wp_apply (hDR l (btIface t) name iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1 ∗ bkSw γ (1 : Qp).half w)
        iprop(lkT γ d q0 W Pk Hk { st with roles := GMap.delete name st.roles } X ∗
          bkSw γ (1 : Qp).half { w with roles := .dels }))
      $$ [$Hp2 $Htx Hlk Hr1 Hsw] as ⟨Hlk, Hsw⟩
    · iframe Hlk Hr1 Hsw
      iintro !> %bk %key !> %Ψ ⟨#Hg, Hkey, Hlk, Hr1, Hsw⟩ HΨ
      ihave #Hbk := schema.authRoles_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_del hDel hRB γ d q0 W Pk Hk t hPw mvcc.authRolesBI (by simp [authBktL, authRolesBI_name]) hP.2.2
        name st { st with roles := GMap.delete name st.roles } X w { w with roles := .dels }
        (fun bs x k h hb => lkOk_delRole name h hb Hc)) $$ [$Hp1 $Hb $Ht] %bk %key %Ψ
        [$Hbk $Hkey $Hlk $Hr1 $Hsw] HΨ
    iapply HΦ
    iframe Hlk Hsw
  -- UnsafeSaveAuthEnabled
  isplitr
  · iintro !> %st %X %b !> %Φ ⟨Hlk, Hr1⟩ HΦ
    wp_apply (hSE l (btIface t) b iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1)
        iprop(lkT γ d q0 W Pk Hk { st with enabled := b } X))
      $$ [$Hp2 $Htx Hlk Hr1] as Hlk
    · iframe Hlk Hr1
      iintro !> %bk %key %val !> %Ψ ⟨#Hg, #Hkey, #Hval, Hlk, Hr1⟩ HΨ
      ihave #Hbk := schema.auth_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_putA hUP hRB γ d q0 W Pk Hk t hPw mvcc.authBI (by simp [authBktL, authBI_name]) hP.1
        schema.authEnabledKey (if b then [W8 1] else [W8 0]) (by decide) (by decide) st { st with enabled := b } X
        (fun bs x w k h hb => lkOk_putAuth hPw hP.1 _ _ h hb rfl rfl rfl (authAt_enabled b)))
        $$ [$Hp1 $Hb $Ht] %bk %key %val %Ψ [$Hbk $Hkey $Hval $Hlk $Hr1] HΨ
    iapply HΦ
    iexact Hlk
  -- UnsafeSaveAuthRevision
  isplitr
  · iintro !> %st %X %rev !> %Φ ⟨Hlk, Hr1⟩ HΦ
    wp_apply (hSR l (btIface t) rev iprop(lkT γ d q0 W Pk Hk st X ∗ ⧗ 1)
        iprop(lkT γ d q0 W Pk Hk { st with revision := uint.nat rev } X))
      $$ [$Hp2 $Htx Hlk Hr1] as Hlk
    · iframe Hlk Hr1
      iintro !> %bk %key %val !> %Ψ ⟨#Hg, #Hkey, #Hval, Hlk, Hr1⟩ HΨ
      ihave #Hbk := schema.auth_isBucket hID hName hSafe bk $$ [$Hp2 $Hg]
      iapply (lk_putA hUP hRB γ d q0 W Pk Hk t hPw mvcc.authBI (by simp [authBktL, authBI_name]) hP.1
        schema.authRevisionKey (u64Be rev) (by decide) (by decide) st { st with revision := uint.nat rev } X
        (fun bs x w k h hb => lkOk_putAuth hPw hP.1 _ _ h hb rfl rfl rfl (authAt_revision rev)))
        $$ [$Hp1 $Hb $Ht] %bk %key %val %Ψ [$Hbk $Hkey $Hval $Hlk $Hr1] HΨ
    iapply HΦ
    iexact Hlk
  -- Unlock
  isplitr
  · iintro !> %st %X %w !> %Φ ⟨Hlk, Hsw, HI, Hw1, Hw2⟩ HΦ
    wp_apply (hUn l (btIface t)
        iprop(lkT γ d q0 W Pk Hk st X ∗ bkSw γ (1 : Qp).half w ∗ auth.authLockI (.on γ.γa) st ∗
          wbTok d.γB ∗ wbTok d.γB)
        (unC γ d q0 Hk X (wbTok d.γB)) iprop(X ∗ auth.authWTok γ.γc ∗ Hk))
      $$ [$Hp2 $Htx Hlk Hsw HI Hw1 Hw2] as ⟨HX, HW, HHk⟩
    · iframe Hlk Hsw HI Hw1 Hw2
      isplitl
      · iapply Hunl $$ %st %X %w %(wbTok d.γB)
      · iapply Hcom
    iapply HΦ
    iframe HX
    iapply hT.2
    iframe HW HHk
  iframe HGUX HGRX

/-- **A borrow ends** (after `ForceCommit`, the open share borrowed with the write token, `real_borrow`): the buckets
idle again at the history's last state, re-recorded at its last index; the write token taken out. -/
theorem real_unborrow (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (cs : GoString → BktData)
    (hs : List auth.AuthState) (rc : GMap GoString BktData) (w : auth.AuthSess) (st : auth.AuthState)
    (hl : hs.getLast? = some st)
    (hv : viewAt ⟨st, st, st⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩)
    (hrc : ∀ n, n ∈ authBktL → bktOf rc n = cs n) :
    realInv (GF := GF) γ d s0 q0 ∗ bkTok γ (1 : Qp).half (csT cs) ∗ auth.authLockQ γ.γa hs ∗
      rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗ bkSw γ 1 w ∗ bOpen d.γB q0 ⊢ |={⊤}=> auth.authWTok γ.γc := by
  iintro ⟨#Hinv, Hx, Hlq, Hro, Hsw, Hq⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs', %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq', HT, >Hbt⟩ | ⟨Hcur, Hr, Hpr, HT, >Hbt⟩)
  rotate_left
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ _ y $$ [$Hx $Hbt]
  · iunfold batchTok at Hbt
    icases Hbt with ⟨%y, Hbt⟩
    iexfalso; iapply bkTok_half_one γ _ y $$ [$Hx $Hbt]
  icases Hb with (Hid | Hbb)
  · iunfold bkIdle at Hid
    icases Hid with ⟨%hs', %rc', %w', -, -, >Hbt, -, -, -⟩
    iexfalso; iapply bkTok_half_one γ _ _ $$ [$Hx $Hbt]
  iunfold bkBatch at Hbb
  icases Hbb with ⟨>HT, >Hbt⟩
  iunfold bkTok at Hx Hbt
  icombine Hx Hbt gives %Hxe
  obtain ⟨-, Hxe⟩ := Hxe
  have ha : cs' go!"auth" = cs go!"auth" := (congrArg (fun t => t.1) Hxe).symm
  have hu : cs' go!"authUsers" = cs go!"authUsers" := (congrArg (fun t => t.2.1) Hxe).symm
  have hr : cs' go!"authRoles" = cs go!"authRoles" := (congrArg (fun t => t.2.2) Hxe).symm
  iunfold bkCommon at Hc
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >%Hv⟩
  icases lockQ_rec γ.γa hs st hl $$ Hlq with ⟨Hlq, #HsL⟩
  icases lockQ_idx γ.γa hs ju su $$ [$Hlq $Hsu] with ⟨Hlq, %Hju⟩
  ihave Hbt := (ghostVar_split_half γ.γk 1 (csT cs')).2 $$ [Hx Hbt]
  · rw [← Hxe]; iframe Hx Hbt
  imod Hclose $$ [Ha Hu Hr' Hs Hr Hp Hbt Hlq Hro Hsw Hq] with -
  · inext
    iunfold realSt
    iexists cs', st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr']
    · iunfold bkCommon
      iframe Ha Hu Hr'
      iframe #
      ipureintro
      obtain ⟨-, -, -, hpu, -⟩ := Hv
      refine ⟨?_, Nat.le_refl _, Nat.le_refl _, by omega, by omega⟩
      rw [ha, hu, hr]; exact hv
    ileft
    iframe Hs Hr Hp
    ileft
    iunfold bkIdle
    iexists hs, rc, w
    iframe Hlq Hro Hsw Hq
    iunfold bkTok
    iframe Hbt
    ipureintro
    refine ⟨hl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro n hn
    rw [hrc n hn]
    simp only [authBktL, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ha.symm
    · exact hu.symm
    · exact hr.symm
  imodintro
  iexact HT

/-- **`ForceCommit()`** of the backend with the write token, the hook's share and a write-back token: the open share
borrowed from the idle branch (`real_borrow`) for the commit, then given back (`real_unborrow`). -/
theorem real_forceCommit (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ⊢
      {{ (auth.authWTok γ.γc ∗ Hk) ∗ wbTok d.γB }}
        (App (Val #(methods (schema.beIface d.be).ty go!"ForceCommit" (schema.beIface d.be).v)) (Val #()))
      {{ RET #(); auth.authWTok γ.γc ∗ Hk }} := by
  iintro ⟨#Hpkg, #Hb, #Hinv⟩ !> %Φ ⟨⟨HT, HHk⟩, Hw⟩ HΦ
  imod real_borrow γ d s0 q0 $$ [$Hinv $HT] with ⟨%cs, %hs, %rc, %w, %st, Hlq, Hro, Hbt, Hsw, Hq, %Hbr⟩
  iapply wp_fupd
  wp_apply (hFC d.γB d.P W Pk d.be q0 iprop(True) iprop(True)) $$ [$Hb $Hq $Hw] as ⟨Hq, -⟩
  · isplitr
    · itrivial
    iapply commitReq_true
  imod real_unborrow γ d s0 q0 cs hs rc w st Hbr.1 Hbr.2.1 Hbr.2.2 $$ [$Hinv $Hbt $Hlq $Hro $Hsw $Hq] with HT
  imodintro
  iapply HΦ
  iframe HT HHk

/-! ## `GetAllRoles` -/

/-- A non-empty name is not below `"\x00"`. -/
theorem le_zero_of_ne_nil (n : GoString) (h : n ≠ []) : go.GoStringLe [W8 0] n := by
  match n, h with
  | b :: r, _ =>
    by_cases hb : b = W8 0
    · subst hb
      cases r with
      | nil => exact Or.inl rfl
      | cons c r => exact Or.inr ((go.goStringLt_cons_iff _ _ _ _).2 (Or.inr ⟨rfl, go.goStringLt_nil_cons _ _⟩))
    · refine Or.inr ((go.goStringLt_cons_iff _ _ _ _).2 (Or.inl ?_))
      have : uint.Z b ≠ 0 := fun h0 => hb (by apply BitVec.eq_of_toNat_eq; simp only [uint.Z] at h0; simp; omega)
      have : 0 ≤ uint.Z b := by simp only [uint.Z]; omega
      show uint.Z (W8 0) < uint.Z b
      simp only [uint.Z] at *; simp; omega

/-- **The names of schema's range of the roles bucket `m` are listed** (`auth.rolesListed`) of a state `st` whose
roles `m` holds: the window `[0x00, 0xff)` of the sorted entries, at most `2 ^ 63 - 1` of them. -/
theorem rolesListed_range {st : auth.AuthState} {m : BktData} {dR : GoString → auth.RoleRec}
    (h : schema.rolesAt st m dR) : auth.rolesListed ((schema.rolesRangeEnts m).map Prod.fst) st := by
  have hne : ([W8 255] : GoString) ≠ [] := by simp
  have hw : schema.rolesRangeEnts m = (mvcc.window (bktEnts m) [W8 0] [W8 255]).take (2 ^ 63 - 1) := by
    unfold schema.rolesRangeEnts
    rw [mvcc.cursorRange_window _ _ _ _ hne]
    rfl
  have hs : entsSorted (bktEnts m) := bktEnts_sorted m
  have hsw : entsSorted (mvcc.window (bktEnts m) [W8 0] [W8 255]) := hs.sublist (mvcc.window_sublist _ _ _)
  have hmem : ∀ e ∈ schema.rolesRangeEnts m, e ∈ bktEnts m ∧ go.GoStringLe [W8 0] e.1 ∧ strLt e.1 [W8 255] := by
    intro e he
    rw [hw] at he
    exact (mvcc.mem_window hs _ _ e).1 (List.mem_of_mem_take he)
  refine ⟨?_, ?_, ?_⟩
  · have hsr : entsSorted (schema.rolesRangeEnts m) := by rw [hw]; exact hsw.sublist (List.take_sublist _ _)
    unfold entsSorted at hsr
    refine (List.pairwise_map.2 hsr).imp ?_
    intro a b hab heq
    subst heq
    exact go.goStringLt_irrefl _ hab
  · intro n hn
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hn
    obtain ⟨h1, h2, h3⟩ := hmem e he
    have hl := (mvcc.mem_bktEnts m e).1 h1
    refine ⟨(h.1 e.1).1 (by rw [hl]; rfl), ?_, h3⟩
    rintro h0
    rw [h0] at h2
    rcases h2 with h2 | h2
    · cases h2
    · exact go.goStringLt_not_nil _ h2
  · intro hlen n hn hrl
    rw [List.length_map] at hlen
    have htk : schema.rolesRangeEnts m = mvcc.window (bktEnts m) [W8 0] [W8 255] := by
      rw [hw] at hlen ⊢
      apply List.take_of_length_le
      rw [List.length_take] at hlen
      omega
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 ((h.1 n).2 hn)
    refine List.mem_map.2 ⟨(n, v), ?_, rfl⟩
    rw [htk]
    exact (mvcc.mem_window hs _ _ _).2 ⟨(mvcc.mem_bktEnts m (n, v)).2 hv, le_zero_of_ne_nil n hrl.1, hrl.2⟩

theorem rolesOutD_list {st : auth.AuthState} {m : BktData} {dR : GoString → auth.RoleRec}
    (h : schema.rolesAt st m dR) :
    ∀ (rs : List Loc) (es : List Ent), (∀ e ∈ es, m.lookup e.1 = some e.2) →
      ([∗list] x ∈ rs.zip es, auth.ownRole (GF := GF) x.1 (dR x.2.1)) ⊢
        [∗list] x ∈ rs.zip (es.map Prod.fst), auth.roleOut x.1 st x.2
  | [], es, _ => by
    simp only [List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | r :: rs, [], _ => by
    simp only [List.map_nil, List.zip_nil_right]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | r :: rs, e :: es, he => by
    simp only [List.map_cons, List.zip_cons_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · have h1 := schema.roleOutD_are (GF := GF) st m r e.1 dR h
      have he1 : m.lookup e.1 = some e.2 := he e List.mem_cons_self
      simp only [schema.roleOutD, he1] at h1
      iapply h1 $$ H1
    · iapply rolesOutD_list h rs es (fun e' h' => he e' (List.mem_cons_of_mem _ h')) $$ H

/-- **What schema's `GetAllRoles` returns is the store's `rolesOut`** of a state whose roles `m` holds. -/
theorem rolesOutD_at {st : auth.AuthState} {m : BktData} {dR : GoString → auth.RoleRec}
    (h : schema.rolesAt st m dR) (s : GoSlice) :
    schema.rolesOutD (GF := GF) s (schema.rolesRangeEnts m) dR ⊢ auth.rolesOut s st := by
  iintro H
  iunfold schema.rolesOutD at H
  icases H with ⟨%rs, Hs, %Hl, Hrs⟩
  iunfold auth.rolesOut
  iexists rs, (schema.rolesRangeEnts m).map Prod.fst
  iframe Hs
  isplitr
  · ipureintro
    exact ⟨by rw [List.length_map]; exact Hl, rolesListed_range h⟩
  have hin : ∀ e ∈ schema.rolesRangeEnts m, m.lookup e.1 = some e.2 := by
    intro e he
    have hs : entsSorted (bktEnts m) := bktEnts_sorted m
    unfold schema.rolesRangeEnts at he
    rw [mvcc.cursorRange_window _ _ _ _ (by simp)] at he
    exact (mvcc.mem_bktEnts m e).1 ((mvcc.mem_window hs _ _ e).1 (List.mem_of_mem_take he)).1
  iapply rolesOutD_list h rs _ hin $$ Hrs

/-- The roles' records of a bucket `m` holding the history's last state (by choice). -/
def dRm (hs : List auth.AuthState) (m : BktData) : GoString → auth.RoleRec :=
  Classical.epsilon (fun dR => ∃ st, hs.getLast? = some st ∧ schema.rolesAt st m dR)

theorem dRm_at {hs : List auth.AuthState} {m : BktData} {st : auth.AuthState} {dR : GoString → auth.RoleRec}
    (hl : hs.getLast? = some st) (h : schema.rolesAt st m dR) : schema.rolesAt st m (dRm hs m) := by
  obtain ⟨st', hl', hr'⟩ := Classical.epsilon_spec (p := fun dR => ∃ st, hs.getLast? = some st ∧
    schema.rolesAt st m dR) ⟨dR, st, hl, h⟩
  rw [hl] at hl'
  cases hl'
  exact hr'

/-- **`GetAllRoles`' token** `garLk γp Z m`: the batch lock at a session whose roles bucket holds `m`, its bbolt
transaction pinned by the one-shot `γp` (set at `Lock`), with `Z` of the session. -/
def garLk (γp : GName) (γB : BNames) (P : BParams) (b : Loc) (Z : BSess → IProp GF) (m : BktData) : IProp GF :=
  iprop(∃ bs : BSess, ⌜bktOf bs.S go!"authRoles" = m⌝ ∗ dghostVar γp DFrac.discard bs.tx ∗
    batchLocked γB P b bs true ∗ Z bs)

/-- A slice of the pinned transaction is readable under `garLk`. -/
theorem gar_rdCapL (γp : GName) (γB : BNames) (P : BParams) (b : Loc) (Z : BSess → IProp GF) (m : BktData)
    (tx : Loc) :
    ∀ (ss : List GoSlice) (es : List Ent),
    dghostVar γp DFrac.discard tx ∗ ([∗list] x ∈ ss.zip (es.map Prod.snd), rdB (GF := GF) γB.db tx x.1 x.2) ⊢
      [∗list] x ∈ ss.zip es, schema.rdCap (garLk γp γB P b Z m) x.1 x.2.2
  | [], es => by
    simp only [List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: ss, [] => by
    simp only [List.map_nil, List.zip_nil_right]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | s :: ss, e :: es => by
    simp only [List.map_cons, List.zip_cons_cons]
    iintro ⟨#Hp, H⟩
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#H1, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iunfold schema.rdCap
      iintro !> Hlk
      iunfold garLk at Hlk
      icases Hlk with ⟨%bs, %Hm, #Hp', Hl, HZ⟩
      ihave %Htx := dghostVar_agree γp tx DFrac.discard bs.tx DFrac.discard $$ Hp Hp'
      icases batchLocked_rdB γB P b { bs with tx := tx } bs s e.2 true $$ [$H1 $Hl] with
        ⟨%dq, Hs, Hback⟩
      · ipureintro; exact Htx.symm
      iexists dq
      iframe Hs
      iintro Hs
      ihave Hl := Hback $$ Hs
      iunfold garLk
      iexists bs
      iframe Hl HZ Hp'
      ipureintro; exact Hm
    · iapply gar_rdCapL γp γB P b Z m tx ss es $$ [$Hp $H]

/-- **The batch transaction's range of the roles bucket under `garLk`** (`schema.authRolesRange`). -/
theorem gar_rolesRange (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (γp : GName) (γB : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (Z : BSess → IProp GF) (m : BktData)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthRoles ↦□ bk ⊢
        isBucket bk mvcc.authRolesBI) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γB P W Pk b ∗ bF go!"batchTx" b ↦□ t ⊢
      schema.authRolesRange (btIface t) (garLk γp γB P b Z m) m := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Ht⟩
  iunfold schema.authRolesRange
  iintro %bk %key %endKey %dk %de !> %Φ ⟨#Hg, Hlk, Hkey, Hend⟩ HΦ
  iunfold garLk at Hlk
  icases Hlk with ⟨%bs, %Hm, #Hp, Hl, HZ⟩
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  ihave %Hlen0 := ownSlice_len endKey de [W8 255] $$ Hend
  have Hne : (endKey = slice.nil ↔ [W8 255] = []) := by
    constructor
    · intro h; subst h; simp at Hlen0; exact absurd Hlen0.1 (by decide)
    · intro h; cases h
  wp_apply (hUR γB P W Pk b t bs bk mvcc.authRolesBI key endKey [W8 0] [W8 255] dk de (W64 (-1)) Hne true)
    $$ [$Hb $Ht $Hl $Hbk $Hkey $Hend] as %ks %vs ⟨Hl, Hkey, Hend, Hout, -⟩
  iunfold kvsOutRd at Hout
  iunfold rdSlices at Hout
  icases Hout with ⟨%ks', %vs', -, -, Hvs, -, -, ⟨%Hlen, Hrd⟩⟩
  iapply HΦ
  iframe Hkey Hend
  isplitl [Hl HZ]
  · iunfold garLk; iexists bs; iframe Hl HZ Hp; ipureintro; exact Hm
  iexists vs'
  iframe Hvs
  isplitr
  · ipureintro
    rw [Hlen, List.length_map, ← Hm]; rfl
  unfold schema.rolesRangeEnts
  rw [← Hm]
  iapply gar_rdCapL γp γB P b Z (bktOf bs.S go!"authRoles") bs.tx vs'
    (cursorRange (bktEnts (bktOf bs.S go!"authRoles")) [W8 0] [W8 255] (W64 (-1)))
  iframe Hp
  irevert Hrd
  rw [show go_etcd_io.etcd.server.v3.storage.schema.authRolesName = go!"authRoles" from rfl]
  iintro Hrd
  iexact Hrd

/-- **The store's `GetAllRoles` clause** (`auth.authBackendReads`' last) at schema's auth backend `abl` over the real
backend, the write token `T = authWTok ∗ Hk`: schema's `GetAllRoles` (`BatchTx()`, `LockInsideApply()` as the write
contract's `Lock`, the range under the lock token with the bbolt transaction pinned at `Lock`, `Unlock()`,
`Commit()`); what it returns is `rolesOut` of the history's last state (`rolesOutD_at`, A6 (R-c)). -/
theorem real_getAllRoles
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF)
    (abl lg : Loc) (dq : DFrac) (f : GoFunc) (T : IProp GF)
    (hT : T ⊣⊢ iprop(auth.authWTok γ.γc ∗ Hk)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ∗ ablOn abl d.be lg ∗
      □ (Hk -∗ plHookAt d.γB dq f ∗ (plHookAt d.γB dq f -∗ Hk)) ⊢
      □ (∀ (hs : List auth.AuthState) (Pre Q Post : IProp GF),
        {{ srvApi.csContractA Pk f Pre Q Post ∗ T ∗ wbTok d.γB ∗ wbTok d.γB ∗ auth.authOwn (.on γ.γa) hs }}
          (App (Val #(methods (ablIface abl).ty go!"GetAllRoles" (ablIface abl).v)) (Val #()))
        {{ (s : GoSlice), RET #s; Post ∗ T ∗ auth.authOwn (.on γ.γa) hs ∗
            ∃ sta : auth.AuthState, ⌜auth.histLast (.on γ.γa) hs sta⌝ ∗ auth.rolesOut s sta }}) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv, #Habl, #Hhk⟩
  iunfold ablOn at Habl
  icases Habl with ⟨#Hbf, #Hlf⟩
  iintro !> %hs %Pre %Q %Post !> %Φ ⟨Hcs, HT, Hw1, Hw2, Hown⟩ HΦ
  icases hT.1 $$ HT with ⟨HT, HHk⟩
  imod (dghostVar_alloc (GF := GF) (A := Loc) null) with ⟨%γp, Hpin⟩
  -- the token's parts besides the batch lock
  let X : BktData → IProp GF := fun m =>
    iprop(Post ∗ auth.authOwn (.on γ.γa) hs ∗
      ⌜∃ sta, hs.getLast? = some sta ∧ schema.rolesAt sta m (dRm hs m)⌝)
  let Z : BktData → BSess → IProp GF := fun m bs =>
    iprop(∃ st : auth.AuthState, lkR γ d q0 W Pk Hk bs st (X m) ∗ bkSw γ (1 : Qp).half auth.AuthSess.init ∗
      auth.authLockI (.on γ.γa) st ∗ wbTok d.γB ∗ wbTok d.γB)
  iapply wp_fupd
  wp_apply (hGARs abl (schema.beIface d.be) lg
      iprop(srvApi.csContractA Pk f Pre Q Post ∗ auth.authWTok γ.γc ∗ Hk ∗ wbTok d.γB ∗ wbTok d.γB ∗
        auth.authOwn (.on γ.γa) hs ∗ dghostVar γp (DFrac.own 1) null)
      (fun m => garLk γp d.γB d.P d.be (Z m) m)
      (fun m => unC γ d q0 Hk (X m) (wbTok d.γB))
      (fun m => iprop(X m ∗ auth.authWTok γ.γc ∗ Hk))
      (dRm hs))
    $$ [$Hp2 $Hbf $Hlf Hcs HT HHk Hw1 Hw2 Hown Hpin] as %s ⟨%m, ⟨⟨HPost, Hown, %Hm⟩, HT, HHk⟩, Hout⟩
  · iframe Hcs HT HHk Hw1 Hw2 Hown Hpin
    iintro %Ψ !> - HΨ
    wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hb] as %t1 #Ht1
    iapply HΨ
    iexists btIface t1
    isplitr
    · ipureintro; rfl
    ihave #Hlock := lk_lock hLI γ d s0 q0 W Pk Hk t1 dq f $$ [$Hp1 $Hb $Ht1 $Hinv $Hhk]
    ihave #Hunl := lk_unlock hUL hRB γ d s0 q0 W Pk Hk t1 $$ [$Hp1 $Hb $Ht1 $Hinv]
    ihave #Hcom := lk_commit hCm γ d s0 q0 W Pk Hk t1 $$ [$Hp1 $Hb $Ht1 $Hinv]
    -- LockInsideApply
    isplitl
    · iintro %Ψ' !> ⟨Hcs, HT, HHk, Hw1, Hw2, Hown, Hpin⟩ HΨ'
      iapply wp_fupd
      wp_apply Hlock $$ %Pre %Q %Post [$Hcs $HT $HHk] as ⟨%st, Hlk, Hsw, HI⟩
      ihave ⟨HoF, %Hl⟩ := auth.authOwn_lockI_join (.on γ.γa) hs st $$ Hown HI
      icases auth.authOwnF_lockI_split (.on γ.γa) hs st Hl $$ HoF with ⟨Hown, HI⟩
      iunfold lkT at Hlk
      icases Hlk with ⟨%bs, Hl', HR⟩
      icases lkR_view γ d q0 W Pk Hk bs st Post $$ HR with ⟨HR, %Hv⟩
      simp only [auth.histLast] at Hl
      have Hr : schema.rolesAt st (bktOf bs.S go!"authRoles") (dRm hs (bktOf bs.S go!"authRoles")) := by
        simp only [authD, mvcc.authBI, mvcc.authUsersBI, mvcc.authRolesBI, auth.BkView.uni] at Hv
        obtain ⟨-, -, ⟨dR, hr⟩⟩ := Hv
        exact dRm_at Hl hr
      imod (dghostVar_update bs.tx γp null) $$ Hpin with Hpin
      imod dghostVar_persist γp 1 bs.tx $$ Hpin with #Hpin
      imodintro
      iapply HΨ'
      iexists bktOf bs.S go!"authRoles"
      isplitr
      · ipureintro; exact schema.rolesAt_dec Hr
      iunfold garLk
      iexists bs
      iframe Hl' Hpin
      isplitr
      · ipureintro; rfl
      iexists st
      iframe Hsw HI Hw1 Hw2
      iunfold lkR at HR
      iunfold lkR
      icases HR with ⟨%x, %w, %k, H1, H2, H3, H4, H5, H6, H7, HPost, H9, %Hok⟩
      iexists x, w, k
      dsimp only [X]
      iframe H1 H2 H3 H4 H5 H6 H7 HPost H9 Hown
      ipureintro
      exact ⟨⟨st, Hl, Hr⟩, Hok⟩
    isplitr
    · iintro %m !>
      iapply gar_rolesRange hUR γp d.γB d.P W Pk d.be t1 (Z m) m (schema.authRoles_isBucket hID hName hSafe)
      iframe #
    isplitr
    · iintro %m %Ψ' !> Hlk HΨ'
      iunfold garLk at Hlk
      icases Hlk with ⟨%bs, -, -, Hl, %st, HR, Hsw, HI, Hw1, Hw2⟩
      wp_apply Hunl $$ %st %(X m) %auth.AuthSess.init %(wbTok d.γB) [Hl HR Hsw HI Hw1 Hw2] as HC
      · iframe Hsw HI Hw1 Hw2
        iunfold lkT; iexists bs; iframe Hl HR
      iapply HΨ'; iexact HC
    · iintro %m %Ψ' !> HC HΨ'
      wp_apply Hcom $$ %(X m) [$HC] as HQ
      iapply HΨ'; iexact HQ
  obtain ⟨sta, Hl, Hr⟩ := Hm
  imodintro
  iapply HΦ
  iframe HPost Hown
  isplitl [HT HHk]
  · iapply hT.2; iframe HT HHk
  iexists sta
  isplitr
  · ipureintro; exact Hl
  iapply rolesOutD_at Hr s $$ Hout

/-- **Schema's auth backend over the real backend meets the store's write side** (`auth.authWBackendOkR` in `on γa`,
at the hook `f`, the write token `T = authWTok ∗ Hk`): `BatchTx()` is schema's over the backend's batch transaction
(`real_batchTxLkR`), `ForceCommit()` borrows the open share (`real_forceCommit`), the reads are the reserved pool's
(`real_reads3`) and `GetAllRoles` schema's batch transaction (`real_getAllRoles`). -/
theorem real_wbackendOkR
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk Hk : IProp GF) (hPw : d.P.Wf) (hP : schema.authHas d.P)
    (abl lg : Loc) (dq : DFrac) (f : GoFunc) (T : IProp GF)
    (hT : T ⊣⊢ iprop(auth.authWTok γ.γc ∗ Hk)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ∗ ablOn abl d.be lg ∗
      □ (Hk -∗ plHookAt d.γB dq f ∗ (plHookAt d.γB dq f -∗ Hk)) ⊢
      auth.authWBackendOkR (authBkIface abl) (.on γ.γa) Pk f T (wbTok d.γB) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv, #Habl, #Hhk⟩
  ihave #Hgar := real_getAllRoles hGARs hBT hLI hUL hCm hUR hID hName hSafe hRB γ d s0 q0 W Pk Hk abl lg dq f T hT
    $$ [$Hp1 $Hp2 $Hb $Hinv $Habl $Hhk]
  ihave ⟨#HGU, #HGR, #HGA⟩ := real_reads3 hRT hRL hRU hURr hFEr hID hName hSafe hGUb hGRb hGAb γ d s0 q0 W Pk hP
    Hk abl lg $$ [$Hp1 $Hp2 $Hb $Hinv $Habl]
  ihave #HFC := real_forceCommit hFC γ d s0 q0 W Pk Hk $$ [$Hp1 $Hb $Hinv]
  iunfold ablOn at Habl
  icases Habl with ⟨#Hbf, #Hlf⟩
  iunfold auth.authWBackendOkR
  iexists ablIface abl
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ !> - HΦ
    wp_apply (hBTs abl (schema.beIface d.be) lg
        (fun t' => iprop(∃ t0 : Loc, ⌜t' = btIface t0⌝ ∗ bF go!"batchTx" d.be ↦□ t0)))
      $$ [$Hp2 $Hbf $Hlf] as %tx ⟨%l, %t', %Htx, #Htxf, #Hlgf, ⟨%t0, %Ht', #Ht0⟩⟩
    · iintro %Ψ !> - HΨ
      wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hb] as %t1 #Ht1
      iapply HΨ
      iexists btIface t1
      isplitr
      · ipureintro; rfl
      iexists t1
      iframe Ht1
      ipureintro; rfl
    subst Ht'
    iapply HΦ
    iunfold auth.authBatchTxOkR
    iexists abtIface l
    isplitr
    · ipureintro; exact Htx
    iexists lkT γ d q0 W Pk Hk, (fun w => bkSw γ (1 : Qp).half w)
    iapply real_batchTxLkR hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hLI hUL hCm hUP hDel hUR hFE hID
      hName hSafe hRB γ d s0 q0 W Pk Hk hPw hP l t0 lg dq f T hT
    iframe #
  isplitr
  · iintro !> %Φ !> ⟨HT, Hw⟩ HΦ
    wp_apply (hFCs abl (schema.beIface d.be) iprop((auth.authWTok γ.γc ∗ Hk) ∗ wbTok d.γB)
        iprop(auth.authWTok γ.γc ∗ Hk)) $$ [$Hp2 $Hbf HT Hw] as HT
    · isplitl [HT Hw]
      · iframe Hw; iapply hT.1 $$ HT
      iexact HFC
    iapply HΦ
    iapply hT.2 $$ HT
  iunfold auth.authBackendReads
  isplitr
  · iintro !> %hs %name !> %Φ ⟨HT, Ho⟩ HΦ
    iapply HGU $$ %hs %name %Φ [HT Ho]
    · iframe Ho; iapply hT.1 $$ HT
    inext
    iintro %u ⟨HT, Ho, Hu⟩
    iapply HΦ
    iframe Ho Hu
    iapply hT.2 $$ HT
  isplitr
  · iintro !> %hs %name !> %Φ ⟨HT, Ho⟩ HΦ
    iapply HGR $$ %hs %name %Φ [HT Ho]
    · iframe Ho; iapply hT.1 $$ HT
    inext
    iintro %u ⟨HT, Ho, Hu⟩
    iapply HΦ
    iframe Ho Hu
    iapply hT.2 $$ HT
  isplitr
  · iintro !> %hs !> %Φ ⟨HT, Ho⟩ HΦ
    iapply HGA $$ %hs %Φ [HT Ho]
    · iframe Ho; iapply hT.1 $$ HT
    inext
    iintro %u ⟨HT, Ho, Hu⟩
    iapply HΦ
    iframe Ho Hu
    iapply hT.2 $$ HT
  iexact Hgar

/-! ## `CreateAuthBuckets` -/

theorem bktOf_create (bs : BSess) (bi : BucketInfo) (m : GoString) :
    bktOf (bs.create bi).S m = bktOf bs.S m := by
  show bktOf (if bs.S.lookup bi.name = none then bs.S.insert bi.name ∅ else bs.S) m = _
  split
  · rename_i h
    by_cases e : bi.name = m
    · subst e; rw [bktOf_ins]; unfold bktOf; rw [h]; rfl
    · exact bktOf_ins_ne _ _ _ _ e
  · rfl

theorem rbData_create_ne (P : BParams) (bs : BSess) (bi : BucketInfo) (m : GoString) (h : bi.name ≠ m) :
    (rbData P (bs.create bi).S).lookup m = (rbData P bs.S).lookup m := by
  show (rbData P (if bs.S.lookup bi.name = none then bs.S.insert bi.name ∅ else bs.S)).lookup m = _
  split
  · exact rbData_ins_ne P bs.S bi.name m ∅ h
  · rfl

/-- A creation keeps the lock token's facts (it changes no kind and nothing `bktOf` sees). -/
theorem lkOk_create {d : mvcc.KBReal} {bs : BSess} {st : auth.AuthState} {x : BktData × BktData × BktData}
    {w : auth.AuthSess} {k : Nat} (bi : BucketInfo) (h : LkOk d bs st x w k)
    (hp : sint.Z bs.pend + 1 < sint.Z d.P.limit + k + 3) (hb : sint.Z bs.pend + 1 < 2 ^ 58) :
    LkOk d (bs.create bi) st x w k where
  hw := h.hw
  vs := mvcc.viewSame_create bi h.vs
  cw := h.cw
  pend := by
    show sint.Z (bs.pend + W64 1) < _
    have : sint.Z (bs.pend + W64 1) = sint.Z bs.pend + 1 := by word
    omega
  ka := h.ka
  ku := h.ku
  kr := h.kr
  ia := fun e => by rw [bktOf_create]; exact h.ia e
  iu := fun e => by rw [bktOf_create]; exact h.iu e
  ir := fun e => by rw [bktOf_create]; exact h.ir e
  view := by
    have : authD (bs.create bi).S = authD bs.S := by simp only [authD, bktOf_create]
    rw [this]; exact h.view

/-- **`CreateAuthBuckets`' token after `i` creations**: the lock token's parts at a session whose pending writes are
below the backend's limit plus `i`, the session token's half at the start, the lock's share of the history. -/
def lkI (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk X : IProp GF) (i : Nat) : IProp GF :=
  iprop(∃ (st : auth.AuthState) (bs : BSess), ⌜sint.Z bs.pend < sint.Z d.P.limit + i⌝ ∗
    batchLocked d.γB d.P d.be bs true ∗ lkR γ d q0 W Pk Hk bs st X ∗
    bkSw γ (1 : Qp).half auth.AuthSess.init ∗ auth.authLockI (.on γ.γa) st)

/-- **A claimed creation of an auth bucket** under `CreateAuthBuckets`' token (one of three). -/
theorem lk_create (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (q0 : Qp) (W Pk Hk X : IProp GF) (t : Loc) (hPw : d.P.Wf)
    (bi : BucketInfo) (hbi : bi.name ∈ authBktL) (hhas : d.P.has bi) (hn0 : 0 < bi.name.length)
    (hn1 : bi.name.length ≤ maxKeySize) (i : Nat) (hi : i < 3) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend d.γB d.P W Pk d.be ∗ bF go!"batchTx" d.be ↦□ t ⊢
      ∀ bk : GoInterface,
        {{ isBucket bk bi ∗ lkI γ d q0 W Pk Hk X i }}
          (App (Val #(methods (btIface t).ty go!"UnsafeCreateBucket" (btIface t).v)) (Val #bk))
        {{ RET #(); lkI γ d q0 W Pk Hk X (i + 1) }} := by
  iintro ⟨#Hpkg, #Hb, #Ht⟩ %bk !> %Φ ⟨#Hbk, Hlk⟩ HΦ
  iunfold lkI at Hlk
  icases Hlk with ⟨%st, %bs, %Hp, Hl, HR, Hsw, HI⟩
  iunfold lkR at HR
  icases HR with ⟨%x, %w, %k, Hrp, Hx, Hsw0, Hq, HW, HPk, HHk, HX, Hrk, %Hok⟩
  have hlim := hPw.2.2.1
  have hpend : sint.Z bs.pend + 1 < 2 ^ 58 := by omega
  icases (rbPartR_pick d.γB bi.name hbi _).1 $$ Hrp with ⟨Hn, Hrest⟩
  ihave Hrbp := (rbPut_true d.γB d.P bi.name bs.S).2 $$ [Hn]
  · iframe Hn; ipureintro; exact rb_auth d _ hbi
  wp_apply (@hCB d.γB d.P W Pk d.be t bs bk bi hhas hn0 hn1 hpend true true (by decide))
    $$ [$Hb $Ht $Hl $Hbk $Hrbp] as ⟨Hl, Hrbp⟩
  icases (rbPut_true d.γB d.P bi.name _).1 $$ Hrbp with ⟨-, Hn⟩
  ihave Hn := rbPartR_congr d.γB (fun m => m = bi.name)
    (rbData d.P (if bs.S.lookup bi.name = none then bs.S.insert bi.name ∅ else bs.S))
    (rbData d.P (bs.create bi).S) (fun _ _ => rfl) $$ Hn
  ihave Hrest := rbPartR_congr d.γB _ (rbData d.P bs.S) (rbData d.P (bs.create bi).S)
    (fun m hm => (rbData_create_ne d.P bs bi m (fun e => hm.2 e.symm)).symm) $$ Hrest
  ihave Hrp := (rbPartR_pick d.γB bi.name hbi _).2 $$ [$Hn $Hrest]
  iapply HΦ
  iunfold lkI
  iexists st, bs.create bi
  iframe Hl Hsw HI
  isplitr
  · ipureintro
    show sint.Z (bs.pend + W64 1) < _
    have : sint.Z (bs.pend + W64 1) = sint.Z bs.pend + 1 := by word
    push_cast; omega
  iunfold lkR
  iexists x, w, k
  iframe Hrp Hx Hsw0 Hq HW HPk HHk HX Hrk
  ipureintro
  exact lkOk_create bi Hok (by push_cast at Hp ⊢; omega) hpend

/-- **`CreateAuthBuckets` at the boot token** (`authSchemaSrv`'s, A6 STOP decided): the write token with the clients'
half of the unset hook and one write-back token: borrow, `LockOutsideApply()` (no hook), the claim, three claimed
creations, `Unlock()` (`lk_unlock`), and the session returned (no commit: `CreateAuthBuckets` calls none). -/
theorem real_createAuthBuckets
    (hCABs : schema.authBackend.CreateAuthBuckets.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk : IProp GF) (hP : schema.authHas d.P) (abl lg : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ∗ ablOn abl d.be lg ⊢
      {{ (auth.authWTok γ.γc ∗ plHook d.γB func.nil) ∗ wbTok d.γB }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty)
          go!"CreateAuthBuckets" #abl)) (Val #()))
      {{ RET #(); auth.authWTok γ.γc ∗ plHook d.γB func.nil }} := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv, #Habl⟩
  icases isBackend_b d.γB d.P W Pk d.be $$ Hb with ⟨%t', %rt, %db, %lg', -, -, -, -, -, -, -, -, -, -, -, %HPw⟩
  iunfold ablOn at Habl
  icases Habl with ⟨#Hbf, #Hlf⟩
  iintro !> %Φ ⟨⟨HT, HHk⟩, Hw⟩ HΦ
  imod real_borrow γ d s0 q0 $$ [$Hinv $HT] with ⟨%cs, %hs, %rc, %w, %st, Hlq, Hro, Hbt, Hsw, Hq, %Hbr⟩
  let Hk : IProp GF := plHook d.γB func.nil
  let L : Nat → IProp GF := fun i => iprop(lkI γ d q0 W Pk Hk iprop(True) i ∗ wbTok d.γB)
  wp_apply (hCABs abl (schema.beIface d.be)
      iprop(bOpen d.γB q0 ∗ Hk ∗ auth.authLockQ γ.γa hs ∗ rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗
        bkTok γ (1 : Qp).half (csT cs) ∗ bkSw γ 1 w ∗ wbTok d.γB)
      L iprop(auth.authWTok γ.γc ∗ Hk))
    $$ [$Hp2 $Hbf Hq HHk Hlq Hro Hbt Hsw Hw] as ⟨HT, HHk⟩
  · iframe Hq HHk Hlq Hro Hbt Hsw Hw
    iintro %Ψ !> - HΨ
    wp_apply (hBT d.γB d.P W Pk d.be) $$ [$Hb] as %t1 #Ht1
    iapply HΨ
    iexists btIface t1
    isplitr
    · ipureintro; rfl
    ihave #Hunl := lk_unlock hUL hRB γ d s0 q0 W Pk Hk t1 $$ [$Hp1 $Hb $Ht1 $Hinv]
    -- LockOutsideApply, the claim
    isplitl
    · iintro %Ψ' !> ⟨Hq, HHk, Hlq, Hro, Hbt, Hsw, Hw⟩ HΨ'
      iapply wp_fupd
      wp_apply (hLO d.γB d.P W Pk d.be t1 q0) $$ [$Hb $Ht1 $Hq] as ⟨%bs, Hl, %Hfree, ⟨HW, HPk⟩, Hq⟩
      ihave Htr : (True : IProp GF) $$ []
      · itrivial
      imod lk_claim γ d q0 W Pk Hk iprop(True) cs hs rc w st Hbr bs Hfree
        $$ [$Hl $HW $HPk $Htr $Hq $HHk $Hlq $Hro $Hbt $Hsw] with ⟨%st', %bs', %Hp, Hl, HR, Hsw, HI⟩
      imodintro
      iapply HΨ'
      dsimp only [L]
      iframe Hw
      iunfold lkI
      iexists st', bs'
      iframe Hl HR Hsw HI
      ipureintro; push_cast; omega
    -- the three creations
    isplitr
    · iintro %b %Ψ' !> ⟨⟨HL, Hw⟩, #Hg⟩ HΨ'
      ihave #Hbk := schema.auth_isBucket hID hName hSafe b $$ [$Hp2 $Hg]
      wp_apply (lk_create hCB γ d q0 W Pk Hk iprop(True) t1 HPw mvcc.authBI (by simp [authBktL, authBI_name])
        hP.1 (by rw [authBI_name]; decide) (by rw [authBI_name]; decide) 0 (by decide)) $$ [$Hp1 $Hb $Ht1] %b
        [$Hbk $HL] as HL
      iapply HΨ'; dsimp only [L]; iframe Hw; iexact HL
    isplitr
    · iintro %b %Ψ' !> ⟨⟨HL, Hw⟩, #Hg⟩ HΨ'
      ihave #Hbk := schema.authUsers_isBucket hID hName hSafe b $$ [$Hp2 $Hg]
      wp_apply (lk_create hCB γ d q0 W Pk Hk iprop(True) t1 HPw mvcc.authUsersBI
        (by simp [authBktL, authUsersBI_name]) hP.2.1 (by rw [authUsersBI_name]; decide)
        (by rw [authUsersBI_name]; decide) 1 (by decide)) $$ [$Hp1 $Hb $Ht1] %b [$Hbk $HL] as HL
      iapply HΨ'; dsimp only [L]; iframe Hw; iexact HL
    isplitr
    · iintro %b %Ψ' !> ⟨⟨HL, Hw⟩, #Hg⟩ HΨ'
      ihave #Hbk := schema.authRoles_isBucket hID hName hSafe b $$ [$Hp2 $Hg]
      wp_apply (lk_create hCB γ d q0 W Pk Hk iprop(True) t1 HPw mvcc.authRolesBI
        (by simp [authBktL, authRolesBI_name]) hP.2.2 (by rw [authRolesBI_name]; decide)
        (by rw [authRolesBI_name]; decide) 2 (by decide)) $$ [$Hp1 $Hb $Ht1] %b [$Hbk $HL] as HL
      iapply HΨ'; dsimp only [L]; iframe Hw; iexact HL
    -- Unlock, then the session returned
    · iintro %Ψ' !> ⟨HL, Hw⟩ HΨ'
      iunfold lkI at HL
      icases HL with ⟨%st', %bs, -, Hl, HR, Hsw, HI⟩
      iapply wp_fupd
      wp_apply Hunl $$ %st' %iprop(True) %auth.AuthSess.init %iprop(True) [Hl HR Hsw HI Hw] as HC
      · iframe Hsw HI Hw
        iunfold lkT; iexists bs; iframe Hl HR
      iunfold unC at HC
      icases HC with ⟨%bs', %st'', %hs', %w', -, HHk, Hq, -, HRr', Hro, Hsw, %Hv⟩
      iunfold unRr' at HRr'
      icases HRr' with ⟨Hx, Hlq, %hl⟩
      imod real_return γ d s0 q0 bs' st'' hs' w' Hv hl $$ [$Hinv $Hx $Hlq $Hro $Hsw $Hq] with HT
      imodintro
      iapply HΨ'
      iframe HT HHk
  iapply HΦ
  iframe HT HHk

/-- **The write contract at `d`'s frozen hook** (`authWAtHook`, `authSchemaSrv`'s): at any schema auth backend on `d`'s
backend, any hook `f'` frozen (`plHookRO`), the write token `authWTok` alone (`Hk = emp`). -/
theorem real_wAtHook
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (hP : schema.authHas d.P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      realInv γ d s0 q0 ⊢ authWAtHook γ.γa d γ.γc := by
  iintro ⟨#Hp1, #Hp2, #Hinv⟩
  iunfold authWAtHook
  iintro !> %abl' %lg' %W' %Pk' %f' #Habl #Hb #Hpl %-
  icases isBackend_b d.γB d.P W' Pk' d.be $$ Hb with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -, -, -, -, %HPw⟩
  iapply real_wbackendOkR hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB γ d s0 q0 W' Pk' iprop(emp) HPw hP abl' lg' DFrac.discard f'
    (auth.authWTok γ.γc) sep_emp.symm
  iframe #
  iintro !> - -; iempintro

/-- **The boot write contract** (`authSchemaSrv`'s `authWBackendOkR` at the unset hook): the write token with the
clients' half of the unset hook (`Hk = plHook nil`), the hook `nil`. -/
theorem real_wBoot
    (hLk : schema.authBatchTx.Lock.spec (GF := GF) (hG := hG))
    (hUn : schema.authBatchTx.Unlock.spec (GF := GF) (hG := hG))
    (hPU : schema.authBatchTx.UnsafePutUser.spec (GF := GF) (hG := hG))
    (hDU : schema.authBatchTx.UnsafeDeleteUser.spec (GF := GF) (hG := hG))
    (hPR : schema.authBatchTx.UnsafePutRole.spec (GF := GF) (hG := hG))
    (hDR : schema.authBatchTx.UnsafeDeleteRole.spec (GF := GF) (hG := hG))
    (hSE : schema.authBatchTx.UnsafeSaveAuthEnabled.spec (GF := GF) (hG := hG))
    (hSR : schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG))
    (hGU : schema.authBatchTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBatchTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authBatchTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authBatchTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authBatchTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (hBTs : schema.authBackend.BatchTx.spec (GF := GF) (hG := hG))
    (hFCs : schema.authBackend.ForceCommit.spec (GF := GF) (hG := hG))
    (hGUb : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGRb : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGAb : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (hGARs : schema.authBackend.GetAllRoles.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hFC : backend.backend.ForceCommit.spec (GF := GF) (hG := hG))
    (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hURr : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFEr : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hLI : backend.batchTxBuffered.LockInsideApply.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hCm : backend.batchTxBuffered.Commit.spec (GF := GF) (hG := hG))
    (hUP : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hDel : backend.batchTxBuffered.UnsafeDelete.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.batchTxBuffered.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hRB : receiptBound GF ≤ 2 ^ 48)
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk : IProp GF) (hP : schema.authHas d.P) (abl lg : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ∗ ablOn abl d.be lg ⊢
      auth.authWBackendOkR (authBkIface abl) (.on γ.γa) Pk func.nil
        iprop(auth.authWTok γ.γc ∗ plHook d.γB func.nil) (wbTok d.γB) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv, #Habl⟩
  icases isBackend_b d.γB d.P W Pk d.be $$ Hb with ⟨%t', %rt, %db, %lg', -, -, -, -, -, -, -, -, -, -, -, %HPw⟩
  iapply real_wbackendOkR hLk hUn hPU hDU hPR hDR hSE hSR hGU hGR hEn hRev hGA hBTs hFCs hGUb hGRb hGAb hGARs hBT hFC hRT hRL hRU hURr hFEr hLI hUL hCm hUP hDel hUR hFE hID hName hSafe hRB γ d s0 q0 W Pk (plHook d.γB func.nil) HPw hP abl lg
    (DFrac.own (1 : Qp).half) func.nil _ .rfl
  iframe #
  iintro !> Hk
  iframe Hk
  iintro Hk; iexact Hk

/-! ## The lend (`authBkLend`; STOP 6's K-c, decided by etcd-grove-03, 2026-11-19) -/

/-- Eight bytes are the big-endian encoding of what they decode to. -/
theorem u64Be_beToU64 (v : List w8) (h : v.length = 8) : u64Be (beToU64 v) = v := by
  unfold u64Be beToU64
  rw [leToU64_le _ (by simp [h]), List.reverse_reverse]

/-- **The buckets at one state hold it**, once its revision is written (`1 ≤ st.revision`: the revision key is then
present, of 8 bytes, `revWf`). -/
theorem viewAt_bucketsAre {st : auth.AuthState} {D : schema.AuthData} (h : viewAt ⟨st, st, st⟩ D)
    (h1 : 1 ≤ st.revision) : schema.authBucketsAre st D ∧ st.revision < 2 ^ 64 := by
  have hwf := viewAt_wf h
  obtain ⟨⟨hen, hrev, hrw⟩, ⟨dU, hu⟩, ⟨dR, hr⟩⟩ := h
  obtain ⟨v, hv⟩ : ∃ v, D.auth.lookup schema.authRevisionKey = some v := by
    cases hc : D.auth.lookup schema.authRevisionKey with
    | none =>
      exfalso
      have h0 : uint.nat (schema.revisionOf ⟨D.auth, ∅, ∅⟩) = 0 := by
        simp only [schema.revisionOf, hc]; rfl
      dsimp only at hrev
      omega
    | some v => exact ⟨v, rfl⟩
  have h8 : v.length = 8 := hrw v hv
  have hrev' : uint.nat (beToU64 v) = st.revision := by
    have e : schema.revisionOf ⟨D.auth, ∅, ∅⟩ = beToU64 v := by simp only [schema.revisionOf, hv]
    dsimp only at hrev
    rw [← e]; exact hrev
  refine ⟨⟨hwf, (enabledOf_auth D).trans hen, ?_, hu.1, fun n v hl => ⟨dU n, hu.2 n v hl⟩, hr.1,
    fun n v hl => ⟨dR n, hr.2 n v hl⟩⟩, ?_⟩
  · rw [hv, ← hrev', w64_to_nat_id, u64Be_beToU64 v h8]
  · rw [← hrev']; word

/-- **What the lend observes**: the auth buckets of `r`, equal to the claimed part's `rc` there, whose buckets are
the readers' contents `cs` at one state `st` of revision at least 1, hold `st`. -/
theorem lend_bucketsAt {st : auth.AuthState} {r rc : GMap GoString BktData} {cs : GoString → BktData}
    (hv : viewAt ⟨st, st, st⟩ ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩) (h1 : 1 ≤ st.revision)
    (hrc : ∀ n, n ∈ authBktL → bktOf rc n = cs n) (hag : ∀ n, n ∈ authBktL → rc.lookup n = r.lookup n) :
    authBucketsAt st r := by
  have e : ∀ n, n ∈ authBktL → (r.lookup n).getD ∅ = cs n := fun n hn => by
    rw [← hag n hn]; exact hrc n hn
  have hD : authDataOf r = ⟨cs go!"auth", cs go!"authUsers", cs go!"authRoles"⟩ := by
    unfold authDataOf
    rw [e _ (by simp [authBktL]), e _ (by simp [authBktL]), e _ (by simp [authBktL])]
  unfold authBucketsAt
  rw [hD]
  exact viewAt_bucketsAre hv h1

/-- **The lend** (`authBkLend`, `authSchemaSrv`'s and `authSchemaSnap`'s trusted clause; STOP 6, K-c): the write
token and the admin side's half of the history borrow the idle buckets (`real_borrow`, as a batch begins), whose
lock share of the history agrees with the half (so the buckets are at its last state); `RL` keeps what was borrowed
and the half; with the batch lock's `rbOwn r`, the claimed part's eighth of each auth bucket's element agrees with
`r` there (`rbOwnInR_rbOwn_agree`), so `r`'s auth buckets are the readers' contents, which hold the last state
(`viewAt`, revision at least 1: `lend_bucketsAt`); `RL` given back returns the borrow (`real_unborrow`). -/
theorem real_bkLend (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    realInv (GF := GF) γ d s0 q0 ⊢ authBkLend γ.γa γ.γc d := by
  iintro #Hinv
  iunfold authBkLend
  iintro !> %hs %st %hl %h1 HT Hh
  imod real_borrow γ d s0 q0 $$ [$Hinv $HT] with ⟨%cs, %hs', %rc, %w, %st', Hlq, Hro, Hbt, Hsw, Hq, %Hb⟩
  obtain ⟨hl', hv, hrc⟩ := Hb
  ihave %Heq := auth.authHistHalf_lockQ_agree γ.γa hs hs' $$ Hh Hlq
  subst Heq
  have hst : st = st' := by rw [hl] at hl'; exact Option.some.inj hl'
  subst hst
  imodintro
  iexists iprop(auth.authLockQ γ.γa hs ∗ rbOwnInR d.γB (fun n => n ∈ authBktL) rc ∗
    (bkTok γ (1 : Qp).half (csT cs) ∗ bkSw γ 1 w ∗ bOpen d.γB q0 ∗ auth.authHistHalf γ.γa hs))
  isplitl [Hlq Hro Hbt Hsw Hq Hh]
  · iframe Hlq Hro Hbt Hsw Hq Hh
  isplitr
  · iintro !> %r ⟨Hlq, Hro, Hrest⟩ Hown
    icases rbOwnInR_rbOwn_agree d.γB (fun n => n ∈ authBktL) rc r $$ [$Hro $Hown] with ⟨Hro, Hown, %Hag⟩
    iframe Hlq Hro Hrest Hown
    ipureintro
    exact lend_bucketsAt hv h1 hrc Hag
  · iintro ⟨Hlq, Hro, Hbt, Hsw, Hq, Hh⟩
    imod real_unborrow γ d s0 q0 cs hs rc w st hl hv hrc $$ [$Hinv $Hbt $Hlq $Hro $Hsw $Hq] with HT
    imodintro
    iframe HT Hh

end wr

end authReal
end EtcdGrove
end Perennial
