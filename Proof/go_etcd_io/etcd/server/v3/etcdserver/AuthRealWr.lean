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

end authReal
end EtcdGrove
end Perennial
