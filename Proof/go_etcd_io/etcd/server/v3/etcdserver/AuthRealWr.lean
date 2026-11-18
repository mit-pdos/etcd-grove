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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

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
    rdB bs.tx s v ⊢ schema.rdCap (iprop(batchLocked γ P b bs c ∗ Z)) s v := by
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
    ([∗list] x ∈ ss.zip (es.map Prod.snd), rdB (GF := GF) bs.tx x.1 x.2) ⊢
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
    imod kvsOutRd_nil _ bs.tx ks vs $$ Hout with ⟨#Hks, #Hvs⟩
    imodintro
    iapply HΦ
    iframe Hkey Hl HZ
    iunfold schema.pointValsA
    iexact Hvs
  | some v =>
    iintro Hout
    imod kvsOutRd_single _ bs.tx ks vs kb v $$ Hout with ⟨%ksl, %vsl, -, -, #Hvs, #Hrv⟩
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
    iintro !> %i %e %k %v %Hi !> %Ψ ⟨HI, Hlive, -, -, #Hv⟩ HΨ
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
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >Hpq, >%Hv⟩
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
  imod Hclose $$ [Ha Hu Hr' Hpq Hs Hr Hp HT Hbt] with -
  · inext
    iunfold realSt
    iexists v, st, su', sr', hs.length - 1, ju', jr', p
    isplitl [Ha Hu Hr' Hpq]
    · iunfold bkCommon
      iframe Ha Hu Hr' Hpq
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
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >Hpq, >%Hv⟩
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
  imod Hclose $$ [Ha Hu Hr' Hpq Hs Hr Hp HT Hbt] with -
  · inext
    iunfold realSt
    iexists cs, st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr' Hpq]
    · iunfold bkCommon
      iframe Ha Hu Hr' Hpq
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
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >Hpq, >%Hv⟩
  iunfold bkTok at Hbt
  icases (ghostVar_split_half γ.γk 1 (csT cs)).1 $$ Hbt with ⟨Hb1, Hb2⟩
  imod Hclose $$ [Ha Hu Hr' Hpq Hs Hr Hp HT Hb1] with -
  · inext
    iunfold realSt
    iexists cs, sa, su, sr, ja, ju, jr, p
    isplitl [Ha Hu Hr' Hpq]
    · iunfold bkCommon
      iframe Ha Hu Hr' Hpq
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
  icases Hc with ⟨>Ha, >Hu, >Hr', >#Hsa, >#Hsu, >#Hsr, >Hpq, >%Hv⟩
  icases lockQ_rec γ.γa hs st hl $$ Hlq with ⟨Hlq, #HsL⟩
  icases lockQ_idx γ.γa hs ju su $$ [$Hlq $Hsu] with ⟨Hlq, %Hju⟩
  ihave Hbt := (ghostVar_split_half γ.γk 1 (csT cs)).2 $$ [Hx Hbt]
  · rw [← Hxe]; iframe Hx Hbt
  imod Hclose $$ [Ha Hu Hr' Hpq Hs Hr Hp Hbt Hlq Hro Hsw Hq] with -
  · inext
    iunfold realSt
    iexists cs, st, st, st, hs.length - 1, hs.length - 1, hs.length - 1, p
    isplitl [Ha Hu Hr' Hpq]
    · iunfold bkCommon
      iframe Ha Hu Hr' Hpq
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

end wr

end authReal
end EtcdGrove
end Perennial
