/-
**The auth backend's read side over the real backend** (auth-schema-srv A6, 2026-11-17): schema's
read contracts (`schema.authReader`, `authRTx`, `authBE`, `InvAuthBackend.lean`) met by the backend's
shared read transaction (`readTx`). A held read transaction at the readers' state `rv` reads the auth
buckets `rvAuth P rv` (`rvBkt` of each): its point reads through `readTx.UnsafeRange` (`rtRange_single`),
its walk of `AuthUsers` through `readTx.UnsafeForEach` (`rtForEach`, a permutation of the bucket's
entries: `rtForEach_perm`). The token is `rtHeld … rv ∗ X` for any `X` (what a realization keeps beside
the read lock); `RLock`/`RUnlock` go through the caller's ghost steps (`authBE_real`: the ticket's
redemption for a reader slot and a share of the backend's open token, the observation of the buckets'
well-formedness), so that this file states no realization. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode backend

theorem strLt_irrefl' (a : GoString) : ¬ strLt a a := fun h => go.goStringLt_asymm h h

/-! ## The walk's entries -/

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]


theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  rw [List.Nodup, List.pairwise_map] at h
  exact h.imp (fun hne heq => hne (congrArg f heq))

theorem sorted_keys_nodup {es : List Ent} (h : entsSorted es) : (es.map Prod.fst).Nodup := by
  unfold entsSorted at h
  rw [List.Nodup, List.pairwise_map]
  exact h.imp (fun {a b} (hlt : strLt a.1 b.1) (heq : a.1 = b.1) => strLt_irrefl' b.1 (heq ▸ hlt))

/-- In sorted entries, an entry is the last value of its key. -/
theorem sorted_mem_iff {es : List Ent} (h : entsSorted es) (k v : GoString) :
    (k, v) ∈ es ↔ lastVal es k = some v := by
  induction es with
  | nil => simp [lastVal]
  | cons e l ih =>
    have hl : entsSorted l := (List.pairwise_cons.1 h).2
    have hlt : ∀ x ∈ l, strLt e.1 x.1 := (List.pairwise_cons.1 h).1
    rw [lastVal_cons, List.mem_cons, ih hl]
    obtain ⟨e1, e2⟩ := e
    by_cases he : e1 = k
    · subst he
      have hn : lastVal l e1 = none :=
        lastVal_eq_none (fun x hx hx' => strLt_irrefl' e1 (hx' ▸ hlt x hx))
      rw [hn]
      simp only [↓reduceIte, Option.none_or, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · rintro (h | h)
        · exact h.symm
        · cases h
      · intro h; exact Or.inl h.symm
    · simp only [he, ↓reduceIte, Option.or_none, Prod.mk.injEq]
      constructor
      · rintro (h | h)
        · exact absurd h.1.symm he
        · exact h
      · intro h; exact Or.inr h

theorem mem_bktEnts_iff (m : BktData) (k v : GoString) : (k, v) ∈ bktEnts m ↔ m.lookup k = some v := by
  unfold bktEnts
  rw [(List.mergeSort_perm m.toList entLe).mem_iff]
  exact GMap.mem_toList m k v

theorem bktEnts_nodup (m : BktData) : (bktEnts m).Nodup :=
  nodup_of_map Prod.fst (sorted_keys_nodup (bktEnts_sorted m))

/-- The read buffer's entries of a table bucket are sorted (`rv.2.Wf`). -/
theorem bkOf_sorted {rv : RView} (hw : rv.2.Wf) (i : w64) : entsSorted (bkOf rv.2.bks i) := by
  unfold bkOf
  cases h : rv.2.bks.lookup i with
  | none => exact List.Pairwise.nil
  | some es => exact hw i es h

/-- **A read transaction's walk visits the readers' view of the bucket**: `rtForEach` holds exactly
the entries of `rvBkt` (a table bucket, the read buffer canonical). -/
theorem rtForEach_mem {P : BParams} {rv : RView} {bi : BucketInfo} (hb : P.has bi) (hw : rv.2.Wf)
    (k v : GoString) : (k, v) ∈ rtForEach rv bi ↔ (rvBkt P rv bi.name).lookup k = some v := by
  have hs := bkOf_sorted hw bi.id
  rw [rvBkt_lookup]
  have hvOf : vOf P rv bi.name k =
      (lastVal (bkOf rv.2.bks bi.id) k).or ((bktOf rv.1 bi.name).lookup k) := by
    unfold vOf ovB
    unfold BParams.has at hb
    rw [hb]
    congr 1
    unfold dget bktOf
    cases rv.1.lookup bi.name <;> rfl
  rw [hvOf]
  unfold rtForEach
  rw [List.mem_append, List.mem_filter, mem_bktEnts_iff, sorted_mem_iff hs]
  have hkeys : k ∈ (bkOf rv.2.bks bi.id).map Prod.fst ↔ (lastVal (bkOf rv.2.bks bi.id) k).isSome := by
    constructor
    · intro hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      have : (e.1, e.2) ∈ bkOf rv.2.bks bi.id := he
      rw [sorted_mem_iff hs] at this
      rw [this]; rfl
    · intro hs'
      obtain ⟨e, he, rfl⟩ := lastVal_isSome_mem hs'
      exact List.mem_map.2 ⟨e, he, rfl⟩
  simp only [decide_eq_true_eq]
  rw [hkeys]
  cases hl : lastVal (bkOf rv.2.bks bi.id) k with
  | none => simp
  | some w =>
    simp only [Option.isSome_some, not_true_eq_false, and_false, false_or, Option.some_or]

theorem rtForEach_nodup {rv : RView} {bi : BucketInfo} (hw : rv.2.Wf) :
    (rtForEach rv bi).Nodup := by
  have hs := bkOf_sorted hw bi.id
  unfold rtForEach
  rw [List.nodup_append]
  refine ⟨(bktEnts_nodup _).filter _, nodup_of_map Prod.fst (sorted_keys_nodup hs), ?_⟩
  intro a ha b hb' hab
  subst hab
  have := (List.mem_filter.1 ha).2
  simp only [decide_eq_true_eq] at this
  exact this (List.mem_map.2 ⟨a, hb', rfl⟩)

/-- **The walk is a permutation of the bucket's entries.** -/
theorem rtForEach_perm {P : BParams} {rv : RView} {bi : BucketInfo} (hb : P.has bi) (hw : rv.2.Wf) :
    (rtForEach rv bi).Perm (bktEnts (rvBkt P rv bi.name)) := by
  apply (List.perm_ext_iff_of_nodup (rtForEach_nodup hw) (bktEnts_nodup _)).2
  intro ⟨k, v⟩
  rw [rtForEach_mem hb hw, mem_bktEnts_iff]

end pure

/-! ## The auth buckets of a readers' state -/

/-- **The auth buckets a reader at the readers' state `rv` reads.** -/
def rvAuth (P : BParams) (rv : RView) : AuthData :=
  ⟨rvBkt P rv mvcc.authBI.name, rvBkt P rv mvcc.authUsersBI.name, rvBkt P rv mvcc.authRolesBI.name⟩

/-- The backend's table has the three auth buckets. -/
def authHas (P : BParams) : Prop :=
  P.has mvcc.authBI ∧ P.has mvcc.authUsersBI ∧ P.has mvcc.authRolesBI

section ifaces
variable [GooseExts] [GoGlobalContext]

/-- The shared read transaction `rt` as a `backend.ReadTx` (and an `UnsafeReader`). -/
abbrev rtIface (rt : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty, #rt⟩

/-- The backend `b` as a `backend.Backend`. -/
abbrev beIface (b : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty, #b⟩

end ifaces

/-! ## The auth buckets are `Bucket`s -/

section buckets
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- schema's `Auth` bucket is the `Bucket` `authBI`. -/
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

/-- schema's `AuthUsers` bucket is the `Bucket` `authUsersBI`. -/
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

/-- schema's `AuthRoles` bucket is the `Bucket` `authRolesBI`. -/
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

/-! ## The token of a held read and its slices -/

section read
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The token of a held read in the session of bbolt's transaction `x`, of the auth buckets
`D`**: the shared read transaction held at a readers' state `rv` whose auth buckets are `D`, and the
caller's `Y rv` (what a realization keeps beside the read lock). -/
def heldR (γ : BNames) (P : BParams) (b : Loc) (Y : RView → IProp GF) (x : Loc) (D : AuthData) :
    IProp GF :=
  iprop(∃ rv : RView, ⌜rvAuth P rv = D ∧ rv.2.Wf⌝ ∗ rtHeld γ P b x rv ∗ Y rv)

/-- A held read lends a quarter of bbolt's transaction. -/
theorem rtHeld_lendQ (γ : BNames) (P : BParams) (b x : Loc) (rv : RView) :
    rtHeld (GF := GF) γ P b x rv ⊢
      rtHeldF γ P b x rv sync.rfrac.half.half ∗ txLive x sync.rfrac.half.half := by
  rw [rtHeld_eq]
  conv => lhs; rw [← Qp.half_add_half sync.rfrac.half]
  exact rtHeldF_lend' γ P b x rv _ _

/-- The lent quarter back. -/
theorem rtHeld_returnQ (γ : BNames) (P : BParams) (b x : Loc) (rv : RView) :
    rtHeldF (GF := GF) γ P b x rv sync.rfrac.half.half ∗ txLive x sync.rfrac.half.half ⊢
      rtHeld γ P b x rv := by
  rw [rtHeld_eq]
  conv => rhs; rw [← Qp.half_add_half sync.rfrac.half]
  exact rtHeldF_return γ P b x rv _ _

/-- **A slice a read in the session `x` returned is readable under the token of any held read in
that session** (`rdCap`): the token lends a quarter of bbolt's transaction (`rdB_acc`). -/
theorem heldR_rdCap (γ : BNames) (P : BParams) (b : Loc) (Y : RView → IProp GF) (x : Loc)
    (D : AuthData) (s : GoSlice) (v : GoString) :
    rdB x s v ⊢ rdCap (heldR γ P b Y x D) s v := by
  iintro #Hr
  iunfold rdCap
  iintro !> Hh
  iunfold heldR at Hh
  icases Hh with ⟨%rv, %Hrv, Hh, HY⟩
  icases rtHeld_lendQ γ P b x rv $$ Hh with ⟨Hh, Hl⟩
  icases rdB_acc x s v _ $$ [$Hr $Hl] with ⟨%dq, Hs, Hcl⟩
  iexists dq
  iframe Hs
  iintro Hs
  ihave Hl := Hcl $$ Hs
  ihave Hh := rtHeld_returnQ γ P b x rv $$ [$Hh $Hl]
  iunfold heldR
  iexists rv
  iframe Hh HY
  ipureintro; exact Hrv

/-- **A point read of a held read transaction** (`authPointSpec`): `readTx.UnsafeRange` of one key
of the auth bucket `bi` (in the table, at the global `bv`), the key's entry of the readers' contents
`sel D`. -/
theorem heldR_point (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (Y : RView → IProp GF) (x : Loc)
    (D : AuthData) (bv : GoString) (bi : BucketInfo) (sel : AuthData → BktData)
    (hb : P.has bi) (hsel : ∀ rv, sel (rvAuth P rv) = rvBkt P rv bi.name)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr bv ↦□ bk ⊢ isBucket bk bi) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      authPointSpec (rtIface rt) bv (heldR γ P b Y x D) (sel D) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt⟩
  iunfold authPointSpec
  iintro %bk %key %kb %dq !> %Φ ⟨#Hg, Hh, Hkey⟩ HΦ
  iunfold heldR at Hh
  icases Hh with ⟨%rv, %Hrv, Hh, HY⟩
  obtain ⟨HD, Hwf⟩ := Hrv
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  have h := hUR γ P W Pk b rt x rv sync.rfrac.half bk bi key slice.nil kb [] dq DFrac.discard
    (W64 0) (by simp) (Or.inl (by rw [show rangeLimit [] (W64 0) = W64 1 from rfl]; decide)) hb
  rw [← rtHeld_eq] at h
  iapply wp_fupd
  iapply h $$ %_ [Hh Hkey]
  · iframe Hh Hkey; iframe #
  inext
  iintro %ks %vs ⟨Hh, Hkey, -, Hout⟩
  irevert Hout
  rw [rtRange_single P rv bi kb (W64 0) hb Hwf]
  have hl : (sel D).lookup kb = vOf P rv bi.name kb := by
    rw [← HD, hsel, rvBkt_lookup]
  rw [hl]
  cases hv : vOf P rv bi.name kb with
  | none =>
    iintro Hout
    imod kvsOutRd_nil _ x ks vs $$ Hout with ⟨#Hks, #Hvs⟩
    imodintro
    iapply HΦ
    iframe Hkey
    isplitl [Hh HY]
    · iunfold heldR
      iexists rv
      iframe Hh HY
      ipureintro; exact ⟨HD, Hwf⟩
    iunfold pointValsA
    iexact Hvs
  | some v =>
    iintro Hout
    imod kvsOutRd_single _ x ks vs kb v $$ Hout with ⟨%ksl, %vsl, -, -, #Hvs, #Hrv⟩
    imodintro
    iapply HΦ
    iframe Hkey
    isplitl [Hh HY]
    · iunfold heldR
      iexists rv
      iframe Hh HY
      ipureintro; exact ⟨HD, Hwf⟩
    iunfold pointValsA
    iexists vsl
    iframe Hvs
    ihave #Hc := heldR_rdCap γ P b Y x D vsl v $$ Hrv
    iunfold rdCap at Hc
    iexact Hc

/-- **The walk of `AuthUsers` of a held read transaction** (`authForEachSpec`): `readTx.UnsafeForEach`
visits `rtForEach`, a permutation of the readers' contents (`rtForEach_perm`); the visitor's state
after the `i`-th entry is the caller's at the first `i` entries. -/
theorem heldR_forEach (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (Y : RView → IProp GF) (x : Loc)
    (D : AuthData) (hb : P.has mvcc.authUsersBI)
    (hbk : ∀ bk : GoInterface,
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.schema.AuthUsers ↦□ bk ⊢
        isBucket bk mvcc.authUsersBI) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      authForEachSpec (rtIface rt) go_etcd_io.etcd.server.v3.storage.schema.AuthUsers
        (heldR γ P b Y x D) D.users := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hrt⟩
  iunfold authForEachSpec
  iintro %bk %fn %I !> %Φ ⟨#Hg, Hh, HI, #Hvis⟩ HΦ
  iunfold heldR at Hh
  icases Hh with ⟨%rv, %Hrv, Hh, HY⟩
  obtain ⟨HD, Hwf⟩ := Hrv
  ihave #Hbk := hbk bk $$ [$Hsch $Hg]
  have h := hFE γ P W Pk b rt x rv sync.rfrac.half bk mvcc.authUsersBI fn
    (fun i => I ((rtForEach rv mvcc.authUsersBI).take i)) (fun _ _ => iprop(False))
  rw [← rtHeld_eq] at h
  iapply h $$ %_ [Hh HI] [HY HΦ]
  · iframe Hh; iframe #
    isplitl [HI]
    · simp only [List.take_zero]; iexact HI
    iintro !> %i %e %k %v %Hi !> %Ψ ⟨HI, Hl, #Hk, #Hv⟩ HΨ
    ihave #Hc := heldR_rdCap γ P b Y x D v e.2 $$ Hv
    have ht : (rtForEach rv mvcc.authUsersBI).take (i + 1) =
        (rtForEach rv mvcc.authUsersBI).take i ++ [e] := by
      rw [List.take_add_one, Hi]; rfl
    iapply Hvis $$ %((rtForEach rv mvcc.authUsersBI).take i) %e %k %v %Ψ [HI] [HΨ Hl]
    · iframe HI Hc
    inext
    iintro HI
    iapply HΨ
    iframe Hl
    ileft
    rw [ht]
    iframe HI
    ipureintro; rfl
  inext
  iintro %err ⟨Hh, Hr⟩
  icases Hr with (⟨%Herr, HI⟩ | ⟨%i, -, Hf⟩)
  · iapply HΦ
    isplitr
    · ipureintro; exact Herr
    isplitl [Hh HY]
    · iunfold heldR
      iexists rv
      iframe Hh HY
      ipureintro; exact ⟨HD, Hwf⟩
    iexists rtForEach rv mvcc.authUsersBI
    rw [List.take_length]
    iframe HI
    ipureintro
    rw [← HD]
    exact rtForEach_perm hb Hwf
  · iexfalso; iexact Hf

/-- **A held read transaction is an `UnsafeReader` of the auth buckets `D`** under the token
`heldR … x D`. -/
theorem heldR_reader (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b rt : Loc) (Y : RView → IProp GF) (x : Loc)
    (D : AuthData) (hP : authHas P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ⊢
      authReader (rtIface rt) (heldR γ P b Y x D) D := by
  iintro #H
  iunfold authReader
  isplitr
  · iintro !>
    iapply heldR_point hUR γ P W Pk b rt Y x D _ mvcc.authBI AuthData.auth hP.1
      (fun _ => rfl) (auth_isBucket hID hName hSafe) $$ H
  isplitr
  · iintro !>
    iapply heldR_point hUR γ P W Pk b rt Y x D _ mvcc.authUsersBI AuthData.users hP.2.1
      (fun _ => rfl) (authUsers_isBucket hID hName hSafe) $$ H
  isplitr
  · iintro !>
    iapply heldR_point hUR γ P W Pk b rt Y x D _ mvcc.authRolesBI AuthData.roles hP.2.2
      (fun _ => rfl) (authRoles_isBucket hID hName hSafe) $$ H
  · iintro !>
    iapply heldR_forEach hFE γ P W Pk b rt Y x D hP.2.1 (authUsers_isBucket hID hName hSafe) $$ H

/-- **The real backend is an `authBE`** for the read resource `R` and the lent family `L`, over the
caller's ghost steps, each with a later credit (the caller's invariant holds reader slots, which are not
timeless): `R` with the lent `L i` is redeemed for a reader slot, an open share and the
caller's `C i qo` (`Racq`); after `readTx.RLock` the caller observes, with the held read, the share and
`C i qo`, the lent `L i` back, its `Y rv` and the well-formedness of the auth buckets read (`Robs`); at
`RUnlock` the slot and `Y rv` give `R` back (`Rrel`). The token is `heldR … Y`. -/
theorem authBE_real (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (R : IProp GF) {ι : Type}
    (L : ι → IProp GF) (C : ι → Qp → IProp GF) (Y : RView → IProp GF) (hP : authHas P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend γ P W Pk b ∗
      □ (∀ i : ι, R ∗ L i ∗ £ 1 ={⊤}=∗ ∃ qo : Qp, rdTok γ P b ∗ bOpen γ qo ∗ C i qo) ∗
      □ (∀ (i : ι) (x : Loc) (rv : RView) (qo : Qp), rtHeld γ P b x rv ∗ bOpen γ qo ∗ C i qo ∗ £ 1 ={⊤}=∗
          rtHeld γ P b x rv ∗ L i ∗ Y rv ∗ ⌜authWf (rvAuth P rv)⌝) ∗
      □ (∀ rv : RView, rdTok γ P b ∗ Y rv ∗ £ 1 ={⊤}=∗ R) ⊢
      authBE (beIface b) R L (heldR γ P b Y) := by
  iintro ⟨#Hpkg, #Hsch, #Hb, #Hacq, #Hobs, #Hrel⟩
  iunfold authBE
  iintro !> %Φ !> - HΦ
  wp_apply (hRT γ P W Pk b) $$ [$Hb] as %rt #Hrt
  iapply HΦ
  iexists rtIface rt
  isplitr
  · ipureintro; rfl
  iunfold authRTx
  isplitr
  · iintro !> %i !> %Ψ ⟨HR, HL, Hlc⟩ HΨ
    icases (lc_split (n := 1) (m := 1)).1 $$ Hlc with ⟨Hlc, Hlc1⟩
    imod Hacq $$ %i [$HR $HL $Hlc] with ⟨%qo, Htok, Ho, HC⟩
    iapply wp_fupd
    wp_apply (hRL γ P W Pk b rt qo) $$ [$Hb $Hrt $Htok $Ho] as ⟨%x, %rv, Hh, Ho⟩
    imod Hobs $$ %i %x %rv %qo [$Hh $Ho $HC $Hlc1] with ⟨Hh, HL, HY, %Hawf⟩
    icases rtHeld_wf γ P b x rv $$ Hh with ⟨Hh, %Hwf⟩
    imodintro
    iapply HΨ
    iexists x, rvAuth P rv
    isplitr
    · ipureintro; exact Hawf
    isplitl [Hh HY]
    · iunfold heldR
      iexists rv
      iframe Hh HY
      ipureintro; exact ⟨rfl, Hwf⟩
    iframe HL
    iapply heldR_reader hUR hFE hID hName hSafe γ P W Pk b rt Y x (rvAuth P rv) hP $$
      [$Hpkg $Hsch $Hb $Hrt]
  · iintro !> %x %D !> %Ψ ⟨Hh, Hlc1⟩ HΨ
    iunfold heldR at Hh
    icases Hh with ⟨%rv, -, Hh, HY⟩
    iapply wp_fupd
    wp_apply (hRU γ P W Pk b rt x rv) $$ [$Hb $Hrt $Hh] as Htok
    imod Hrel $$ %rv [$Htok $HY $Hlc1] with HR
    imodintro
    iapply HΨ
    iexact HR

end read

end schema
end EtcdGrove
end Perennial
