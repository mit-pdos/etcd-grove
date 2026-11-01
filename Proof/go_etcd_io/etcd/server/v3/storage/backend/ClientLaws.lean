/-
**The backend's laws for its clients** (the backend-cmp Probe, 2026-10-30;
`notes/spec-first-study/backend-probe.md`, section 4, sites 1-14 and 16-17): what mvcc's and
etcdserver's proofs used to get by unfolding the backend's definitions (the constructor's post,
the compaction keys' resources, the deletable keys' registration, a read's output slices, the
writer's contents' view). Each is stated here, in a module of its own so that adding them leaves
the backend's other modules (and everything importing them) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.CommitLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

/-! ## The compaction keys (pure) -/

/-- **The keys whose absence the backend tracks** (`fkKey`): the `Meta` bucket's (schema's
`metaBucketName`) `scheduledCompactRev` and `finishedCompactRev` (schema's
`ScheduledCompactKeyName`, `FinishedCompactKeyName`). -/
theorem fkKey_iff (n k : GoString) :
    fkKey n k ↔ n = go!"meta" ∧ (k = go!"scheduledCompactRev" ∨ k = go!"finishedCompactRev") :=
  Iff.rfl

/-- Over bbolt's data whose compaction keys hold only well-formed values, the constructor's bit is
`true`. -/
theorem fkWInit_of_wf {P : BParams} {D : Data} (h : fkWfD P D) : fkWInit P D = true := by
  unfold fkWInit; simpa using h

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The compaction keys' resources -/

/-- **What the constructor gives of the compaction keys** (`fkCl`, its parts): the client's half of
their flag at `fkInit D` and the bit at `fkWInit P D`. (Until the M2 storage plan's items 27/29,
2026-10-30, an equivalence: `fkCl` now also records the open, `fkCl_open`.) -/
theorem fkCl_parts (γ : BNames) (P : BParams) (D : Data) :
    fkCl (GF := GF) γ P D ⊢ fkOwn γ (fkInit D) ∗ fkV γ (fkWInit P D) := by
  unfold fkCl fkV fkVR
  iintro ⟨Ho, #Hv⟩
  iframe Ho
  iexists fkInit D, fkVals D
  iexact Hv

/-- **What the constructor gives of the compaction keys, with the open** (the M2 storage plan's
items 27/29, 2026-10-30): the client's half of their flag at `fkInit D`, the bit at `fkWInit P D`,
and the open's record: the flag stood at `fkInit D` over `D`'s compaction-key values
(`fkOpen`, `fkVals`), so that while the client's half stays there every state of the backend
holds them (`fkRd_open`). -/
theorem fkCl_open (γ : BNames) (P : BParams) (D : Data) :
    fkCl (GF := GF) γ P D ⊢
      fkOwn γ (fkInit D) ∗ fkV γ (fkWInit P D) ∗ fkOpen γ (fkInit D) (fkVals D) := by
  unfold fkCl fkV fkOpen fkVR
  iintro ⟨Ho, #Hv⟩
  iframe Ho
  isplitr
  · iexists fkInit D, fkVals D
    iexact Hv
  · iexists fkWInit P D
    iexact Hv

/-- The bit of an open record, at `true` (the merged ghost: `fkV` and `fkOpen` are one ghost). -/
theorem fkOpen_fkV (γ : BNames) (n : Nat) (v : FkVals) :
    fkOpen (GF := GF) γ n v ∗ fkV γ true ⊢ fkVR γ (true, n, v) := by
  unfold fkOpen fkV fkVR
  iintro ⟨⟨%w, #H1⟩, %n', %v', #H2⟩
  ihave %Hag := dghostVar_agree γ.fkv ((w, n, v) : FkG) DFrac.discard ((true, n', v') : FkG)
    DFrac.discard $$ H1 H2
  have hw : w = true := congrArg Prod.fst Hag
  subst hw
  iexact H1

/-- A put of a compaction key needs the client's half of the flag (`fkPut`), at some value. -/
theorem fkPut_of_fk (γ : BNames) (n k : GoString) (h : fkKey n k) :
    fkPut (GF := GF) γ n k = iprop(∃ f : Nat, fkOwn γ f) := by
  unfold fkPut; exact if_pos h

/-- A put of a key no hook owns needs nothing of the hooks' keys (`hkPut`). -/
theorem hkPut_of_not_HK (γ : BNames) (P : BParams) (n k : GoString) (S : Data)
    (h : P.HK n k = false) : ⊢ hkPut (GF := GF) γ P n k S := by
  unfold hkPut BParams.hk
  rw [h]
  simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  iintro; itrivial

/-! ## Thin views and the deletable keys -/

/-- **A thin view, introduced** (the converse of `thinV_sub` and `thinV_dl`). -/
theorem thinV_intro (γ : BNames) (vd L : VData) :
    ⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝ ∗
      □ (∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs γ nk) ⊢
      thinV (GF := GF) γ vd L := by
  iintro ⟨%H, #Hd⟩
  iunfold thinV
  iframe Hd
  ipureintro; exact H

/-- **A deletable key under a registration**: the registered predicate holds of it, later. -/
theorem dlReg_dlIs (γ : BNames) (Φ : GoString × GoString → IProp GF) (nk : GoString × GoString) :
    dlReg γ Φ ∗ dlIs γ nk ⊢ ▷ Φ nk := by
  iintro ⟨#Hr, #Hk⟩
  iunfold dlIs at Hk
  icases Hk with ⟨%Φ', #HΦ', #Hv⟩
  iunfold dlReg at HΦ'
  iunfold dlReg at Hr
  icases HΦ' with ⟨#Hs1, -⟩
  icases Hr with ⟨#Hs2, -⟩
  ihave Heq := saved_pred_agree γ.dlg _ _ Φ' _ nk $$ Hs1 Hs2
  inext
  ihave Hiff := internalEq_iff _ _ $$ Heq
  icases Hiff with ⟨H1, -⟩
  iapply H1
  iexact Hv

/-- **A key is deletable** if the registered predicate holds of it. -/
theorem dlIs_of_dlReg (γ : BNames) (Φ : GoString × GoString → IProp GF) (nk : GoString × GoString) :
    dlReg γ Φ ∗ □ Φ nk ⊢ dlIs γ nk := by
  iintro ⟨#Hr, #Hk⟩
  iunfold dlIs
  iexists Φ
  iframe Hr Hk

end laws

section laws_sem
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The writer's contents' view, at a key** (`sData`): the data's, off the hooks' buckets. -/
theorem sData_lookup (P : BParams) (S : Data) (nk : GoString × GoString) :
    (sData P S).lookup nk = if P.HB nk.1 then none else dget S nk.1 nk.2 := by
  unfold sData
  rw [vData_lookup, vOf_emptyR]

/-! ## A read's output -/

/-- **A slice a read returned** (`rdB`): read-only for good, or bytes of the read transaction. -/
theorem rdB_iff (rtx : Loc) (s : GoSlice) (b : GoString) :
    rdB (GF := GF) rtx s b ⊣⊢ s ↦*□ b ∨ txBytes rtx s b := by
  unfold rdB; exact .rfl

/-- **An empty read's output slices** (`kvsOutRd` of no entry): both empty, made read-only. -/
theorem kvsOutRd_nil (E : CoPset) (rtx : Loc) (keys vals : GoSlice) :
    kvsOutRd (GF := GF) rtx keys vals [] ⊢
      |={E}=> keys ↦*□ ([] : List GoSlice) ∗ vals ↦*□ ([] : List GoSlice) := by
  iintro Hout
  iunfold kvsOutRd at Hout
  icases Hout with ⟨%ks', %vs', Hk, -, Hv, -, #Hrk, #Hrv⟩
  ihave %Hlk := rdSlices_length rtx ks' _ $$ Hrk
  ihave %Hlv := rdSlices_length rtx vs' _ $$ Hrv
  simp only [List.map_nil, List.length_nil, List.length_eq_zero_iff] at Hlk Hlv
  subst Hlk Hlv
  imod ownSlice_persist $$ Hk with #Hk
  imod ownSlice_persist $$ Hv with #Hv
  imodintro
  iframe Hk Hv

/-- **A one-entry read's output slices** (`kvsOutRd` of `(k, v)`): one slice each, made read-only,
read as `k` and `v` (`rdB`). -/
theorem kvsOutRd_single (E : CoPset) (rtx : Loc) (keys vals : GoSlice) (k v : GoString) :
    kvsOutRd (GF := GF) rtx keys vals [(k, v)] ⊢
      |={E}=> ∃ ksl vsl : GoSlice, keys ↦*□ [ksl] ∗ rdB rtx ksl k ∗ vals ↦*□ [vsl] ∗ rdB rtx vsl v := by
  iintro Hout
  iunfold kvsOutRd at Hout
  icases Hout with ⟨%ks', %vs', Hk, -, Hv, -, #Hrk, #Hrv⟩
  ihave %Hlk := rdSlices_length rtx ks' _ $$ Hrk
  ihave %Hlv := rdSlices_length rtx vs' _ $$ Hrv
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at Hlk Hlv
  obtain ⟨ksl, rfl⟩ := List.length_eq_one_iff.1 Hlk
  obtain ⟨vsl, rfl⟩ := List.length_eq_one_iff.1 Hlv
  iunfold rdSlices at Hrk Hrv
  icases Hrk with ⟨-, #Hrk⟩
  icases Hrv with ⟨-, #Hrv⟩
  irevert Hrk Hrv
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left]
  iintro #Hrk #Hrv
  ihave #Hrk1 := BigSepL.bigSepL_singleton.1 $$ Hrk
  ihave #Hrv1 := BigSepL.bigSepL_singleton.1 $$ Hrv
  imod ownSlice_persist $$ Hk with #Hk
  imod ownSlice_persist $$ Hv with #Hv
  imodintro
  iexists ksl, vsl
  iframe Hk Hv Hrk1 Hrv1

end laws_sem

/-! ## The constructor's post, named -/

section named
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The constructor's post, by name** (`newPost`): a client takes what it needs with `iNamed`,
and a conjunct added later breaks no client. The names: `HnB` (the backend), `HnSC` (its stop
channels), `HnOpen` (the clients' whole open token), `HnV` (the clients' whole view, clean),
`HnH` (the post-lock hook, unset), `HnWb` (the write-back tokens), `HnRB` (the tracked buckets'
half), `HnRT` (the reader tokens), `HnDl` (the deletable keys' registration, unfixed), `HnFk` (the
compaction keys' flag and bit), `HnSr` (the safe-range slot). -/
theorem newPost_named (γ : BNames) (P : BParams) (W Pk : BNames → IProp GF) (b : Loc) (D : Data) :
    newPost γ P W Pk b D ⊢
      iprop("#HnB" ∷ isBackend γ P (W γ) (Pk γ) b ∗ "#HnSC" ∷ isStopChans γ b ∗
        "HnOpen" ∷ bOpen γ 1 ∗ "HnV" ∷ bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗
        "HnH" ∷ plHook γ func.nil ∗ "HnWb" ∷ ownToks γ.wb wbInit ∗
        "HnRB" ∷ rbOwn γ (rbData P D) ∗
        "HnRT" ∷ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          rdTok γ P b) ∗
        "HnDl" ∷ dlInit γ ∗ "HnFk" ∷ fkCl γ P D ∗ "HnSr" ∷ srSlot b) := by
  unfold newPost; exact .rfl

/-- **The constructor's post with the payment rights traded, by name** (`newPostK`): as
`newPost_named`, with `HnK` (the traded `K γ`) in place of `HnOpen` and `HnWb`. -/
theorem newPostK_named (γ : BNames) (P : BParams) (W Pk K : BNames → IProp GF) (b : Loc)
    (D : Data) :
    newPostK γ P W Pk K b D ⊢
      iprop("#HnB" ∷ isBackend γ P (W γ) (Pk γ) b ∗ "#HnSC" ∷ isStopChans γ b ∗ "HnK" ∷ K γ ∗
        "HnV" ∷ bViewC γ 1 (vData P (D, ⟨∅, W64 0⟩)) true ∗ "HnH" ∷ plHook γ func.nil ∗
        "HnRB" ∷ rbOwn γ (rbData P D) ∗
        "HnRT" ∷ ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          rdTok γ P b) ∗
        "HnDl" ∷ dlInit γ ∗ "HnFk" ∷ fkCl γ P D ∗ "HnSr" ∷ srSlot b) := by
  unfold newPostK; exact .rfl

end named

end backend
end EtcdGrove
end Perennial
