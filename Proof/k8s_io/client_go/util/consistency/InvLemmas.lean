/-
The consistency store's invariant, its ghost steps (`Defs.lean`; the pure parts are
`InvPure.lean`): each is a view shift opening `consInv` with later credits, at a method's
linearization point or where a pending write lands. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.consistency.InvPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `WroteAt(o, uid, gr, rv)`'s atomic update, closing into `K`. -/
abbrev auWrote (γ : ConsNames) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString)
    (K : IProp GF) : IProp GF :=
  iprop(▷ |={⊤ \ ↑consN, ∅}=> ∃ M, consState γ M ∗
    (consState γ (wroteAtM M o uid gr rv) -∗ |={∅, ⊤ \ ↑consN}=> K))

/-- `EnsureReady(o)`'s atomic update, closing into `K ok`. -/
abbrev auEns (γ : ConsNames) (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF)
    (o : Owner) (K : Bool → IProp GF) : IProp GF :=
  iprop(▷ |={⊤ \ ↑consN, ∅}=> ∃ M, consState γ M ∗
    (∀ ok : Bool, consState γ (if ok then GMap.delete o M else M) ∗
      (if ok then readyRec S G (M !! o) else iprop(True)) -∗ |={∅, ⊤ \ ↑consN}=> K ok))

/-- The record current for `o` is registered, for `o`. -/
theorem lookup_rec (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc} {o : Owner}
    {r : Loc} (qw : Qp) (hWo : W !! o = some r) :
    inv consN (consInv γ T) ∗ £ 1 ∗ ghostVar γ.W qw W ⊢
      |={⊤}=> ghostVar γ.W qw W ∗ ∃ s, isRec γ r s ∗ ⌜s.owner = o⌝ := by
  iintro ⟨#Hinv, Hlc, HWg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  obtain ⟨s, hs, ho⟩ := owner_of_W Hwf hWo
  ihave #Hr := BigSepM.bigSepM_lookup hs $$ Hrecs_p
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv; iexists M, W, R, Vg, P, n, E; iframe; iframe #; ipureintro; exact Hwf
  imodintro
  iframe HWg
  iexists s
  iframe Hr
  ipureintro; exact ho

/-- A slot excludes any other permission for its owner. -/
theorem slot_excl (T : Owner → Qp → IProp GF) {E : GMap Owner EnsSt} {o : Owner} {e : EnsSt}
    (q : Qp) (he : E !! o = some e) :
    tokExcl T ∗ ([∗map] o ↦ _e ∈ E, T o 1) ∗ T o q ⊢ False := by
  iintro ⟨#Hexcl, Hetoks, HT⟩
  ihave Ho := BigSepM.bigSepM_lookup he $$ Hetoks
  iunfold tokExcl at Hexcl
  iapply Hexcl $$ Ho HT

/-- **`WroteAt` finds the owner's record `r` for its UID** (its linearization point): the
abstract state takes the write (`wroteAtM`), which becomes pending; the permission is deposited. -/
theorem wrote_found_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {r : Loc} {s : RecS} {uid : GoString} (gr : GR) (rv : GoString) (q qw : Qp)
    (K : IProp GF) (hWo : W !! o = some r) (huid : s.uid = uid) (hown : s.owner = o) :
    inv consN (consInv γ T) ∗ tokExcl T ∗ £ 1 ∗ £ 1 ∗ ghostVar γ.W qw W ∗ isRec γ r s ∗
      T o q ∗ auWrote γ o uid gr rv K ⊢
      |={⊤}=> ghostVar γ.W qw W ∗ K ∗ ∃ id, pendTok γ id ⟨r, gr, rv, q⟩ := by
  iintro ⟨#Hinv, #Hexcl, Hlc1, Hlc2, HWg, #Hrec, HT, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  iunfold isRec at Hrec
  icases Hrec with ⟨#Hel, -⟩
  ihave %HR := ghost_map_lookup $$ Hrecs Hel
  cases hE : E !! o with
  | some e =>
    iexfalso
    iapply slot_excl T q hE $$ [$Hexcl $Hetoks $HT]
  | none =>
  have Hwf' := wf_found Hwf gr rv q hWo HR hown huid hE
  imod lc_fupd_elim_later $$ Hlc2 HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  iunfold consState at HMc
  icombine HM HMc gives % ⟨_, HMeq⟩
  subst HMeq
  imod ghostVar_update_halves (wroteAtM M o uid gr rv) $$ HM HMc with ⟨HM, HMc⟩
  imod Hcl $$ [HMc] with HK
  · iunfold consState; iexact HMc
  imod ghost_map_insert n ⟨r, gr, rv, q⟩ (fresh_n Hwf) $$ Hpend with ⟨Hpend, Htok⟩
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks HT]
  · inext; iunfold consInv
    iexists wroteAtM M o uid gr rv, W, R, Vg, (<[n := ⟨r, gr, rv, q⟩]> P), n + 1, E
    iframe; iframe #
    isplitl [Hptoks HT]
    · iapply (BigSepM.bigSepM_insert (fresh_n Hwf)).2
      iframe Hptoks
      iexists s
      iframe #
      rw [hown]; iexact HT
    · ipureintro; exact Hwf'
  imodintro
  iframe HWg HK
  iexists n
  iunfold pendTok
  iexact Htok

/-- A string field owned in full is not also held for good. -/
theorem str_excl (l : Loc) (u v : GoString) : (l ↦□ u : IProp GF) ∗ l ↦ v ⊢ False := by
  rw [typedPointsto_unseal_eq, typedPointsto_unseal_eq]
  simp only [typedPointstoDef_heap]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  unfold heapPointsto
  icases H1 with ⟨-, H1⟩
  icases H2 with ⟨-, H2⟩
  icombine H1 H2 gives % ⟨Hv, -⟩
  exact absurd (DFrac.valid_op_own Hv) (by simp)

/-- **`WroteAt` installs a new record `r'`** for its owner (its linearization point), where the
map (`W`) had none or one for another UID: `r'` is registered, the map's mirror becomes
`<[o := r']> W` (the caller holds the write lock's half), the abstract state takes the write,
which becomes pending. -/
theorem wrote_new_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {uid : GoString} (r' vm : Loc) (γv : GName) (gr : GR) (rv : GoString) (q : Qp)
    (K : IProp GF) (hnn : r' ≠ null) :
    inv consN (consInv γ T) ∗ tokExcl T ∗ £ 1 ∗ £ 1 ∗ ghostVar γ.W (1 : Qp).half W ∗
      □ (∀ r0, ⌜W !! o = some r0⌝ -∗ ∃ s0, isRec γ r0 s0 ∗ ⌜s0.uid ≠ uid⌝) ∗
      structFieldRef ownerRecord go!"ownerUID" r' ↦ uid ∗
      structFieldRef ownerRecord go!"versions" r' ↦□ vm ∗
      sync.isMutex (structFieldRef ownerRecord go!"versionsLock" r') (recLockInv ⟨o, uid, vm, γv⟩) ∗
      ghostVar γv (1 : Qp).half (∅ : Vs) ∗
      T o q ∗ auWrote γ o uid gr rv K ⊢
      |={⊤}=> ghostVar γ.W (1 : Qp).half (<[o := r']> W) ∗ K ∗ isRec γ r' ⟨o, uid, vm, γv⟩ ∗
        ∃ id, pendTok γ id ⟨r', gr, rv, q⟩ := by
  iintro ⟨#Hinv, #Hexcl, Hlc1, Hlc2, HWg, #Hold, Huid, #Hvm, #Hmu, Hγv, HT, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  -- `r'` is fresh: a registered record's UID field is held for good
  cases hR' : R !! r' with
  | some s'' =>
    iexfalso
    ihave Hr := BigSepM.bigSepM_lookup hR' $$ Hrecs_p
    iunfold isRec at Hr
    icases Hr with ⟨-, Hp⟩
    iunfold recPhys at Hp
    icases Hp with ⟨-, Hu, -, -⟩
    iapply str_excl $$ [$Hu $Huid]
  | none =>
  cases hV' : Vg !! r' with
  | some V =>
    iexfalso
    ihave Hv := BigSepM.bigSepM_lookup hV' $$ Hvg
    icases Hv with ⟨%s3, #Hel3, -⟩
    ihave %H3 := ghost_map_lookup $$ Hrecs Hel3
    rw [show R.lookup r' = R !! r' from rfl, hR'] at H3
    cases H3
  | none =>
  -- no `EnsureReady` slot for `o`
  cases hE : E !! o with
  | some e =>
    iexfalso
    iapply slot_excl T q hE $$ [$Hexcl $Hetoks $HT]
  | none =>
  -- the old record, if any, is for another UID
  ihave ⟨Hrecs, %hold⟩ : iprop(ghostMapAuth γ.recs 1 R ∗
      ⌜W !! o = none ∨ ∃ r0 s0, W !! o = some r0 ∧ R !! r0 = some s0 ∧ s0.uid ≠ uid⌝) $$ [Hrecs]
  · cases hw : W !! o with
    | none => iframe Hrecs; ipureintro; left; rfl
    | some r0 =>
      icases Hold $$ %r0 %rfl with ⟨%s0, #Hr0, %hne⟩
      iunfold isRec at Hr0
      icases Hr0 with ⟨#Hel0, -⟩
      ihave %H0 := ghost_map_lookup $$ Hrecs Hel0
      iframe Hrecs
      ipureintro; exact Or.inr ⟨r0, s0, rfl, H0, hne⟩
  have Hwf' := wf_new (s' := ⟨o, uid, vm, γv⟩) Hwf gr rv q hold hR' rfl rfl hE
  imod lc_fupd_elim_later $$ Hlc2 HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  iunfold consState at HMc
  icombine HM HMc gives % ⟨_, HMeq⟩
  subst HMeq
  imod ghostVar_update_halves (wroteAtM M o uid gr rv) $$ HM HMc with ⟨HM, HMc⟩
  imod Hcl $$ [HMc] with HK
  · iunfold consState; iexact HMc
  imod ghostVar_update_halves (<[o := r']> W) $$ HWg HW with ⟨HWg, HW⟩
  imod ghost_map_insert_persist r' (⟨o, uid, vm, γv⟩ : RecS) hR' $$ Hrecs with ⟨Hrecs, #Hel⟩
  imod ghost_map_insert n (⟨r', gr, rv, q⟩ : Pend) (fresh_n Hwf) $$ Hpend with ⟨Hpend, Htok⟩
  ipersist Huid
  ihave #Hrec : isRec γ r' ⟨o, uid, vm, γv⟩ $$ []
  · iunfold isRec; iframe #; iunfold recPhys; iframe #; ipureintro; exact hnn
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks HT Hγv]
  · inext; iunfold consInv
    iexists wroteAtM M o uid gr rv, (<[o := r']> W), (<[r' := ⟨o, uid, vm, γv⟩]> R),
      (<[r' := ∅]> Vg), (<[n := ⟨r', gr, rv, q⟩]> P), n + 1, E
    iframe
    isplitr
    · iapply (BigSepM.bigSepM_insert hR').2
      iframe #
    isplitl [Hvg Hγv]
    · iapply (BigSepM.bigSepM_insert hV').2
      iframe Hvg
      iexists ⟨o, uid, vm, γv⟩
      iframe #; iframe
    isplitl [Hptoks HT]
    · iapply (BigSepM.bigSepM_insert (fresh_n Hwf)).2
      iframe Hptoks
      iexists ⟨o, uid, vm, γv⟩
      iframe #; iframe
    · ipureintro; exact Hwf'
  imodintro
  iframe HWg HK Hrec
  iexists n
  iunfold pendTok
  iexact Htok

/-- A registered record's versions (its lock's half) are well formed. -/
theorem rec_vs_wf (γ : ConsNames) (T : Owner → Qp → IProp GF) {r : Loc} {s : RecS} (V : Vs) :
    inv consN (consInv γ T) ∗ £ 1 ∗ isRec γ r s ∗ ghostVar s.γv (1 : Qp).half V ⊢
      |={⊤}=> ghostVar s.γv (1 : Qp).half V ∗ ⌜vsWf V⌝ := by
  iintro ⟨#Hinv, Hlc, #Hrec, Hg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  iunfold isRec at Hrec
  icases Hrec with ⟨#Hel, -⟩
  ihave %HR := ghost_map_lookup $$ Hrecs Hel
  obtain ⟨V0, hV0⟩ := Option.isSome_iff_exists.1 (Hwf.2.2.2.2.1 r (by simp [show R !! r = some s from HR]))
  ihave Hv := (BigSepM.bigSepM_lookup_acc hV0).1 $$ Hvg
  icases Hv with ⟨⟨%s1, #Hel1, Hg1⟩, Hvg⟩
  ihave %Hs := ghostMapElem_agree $$ Hel Hel1
  subst Hs
  icombine Hg Hg1 gives % ⟨_, HV⟩
  subst HV
  imod Hclose $$ [HM HW Hrecs Hvg Hg1 Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv; iexists M, W, R, Vg, P, n, E; iframe; iframe #
    isplitl [Hvg Hg1]
    · iapply Hvg; iexists s; iframe #; iframe
    · ipureintro; exact Hwf
  imodintro
  iframe Hg
  ipureintro; exact Hwf.2.2.2.1 r V hV0

/-- **A pending write lands** (`ownerRecord.WroteAt`, under the record's lock, whose half of the
record's mirror the caller holds): the mirror takes it, the write is no longer pending, the caller
gets its permission back. -/
theorem withdraw_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {r : Loc} {s : RecS}
    {id : Nat} {gr : GR} {rv : GoString} {q : Qp} (V : Vs) :
    inv consN (consInv γ T) ∗ tokExcl T ∗ £ 1 ∗ isRec γ r s ∗ pendTok γ id ⟨r, gr, rv, q⟩ ∗
      ghostVar s.γv (1 : Qp).half V ⊢
      |={⊤}=> ghostVar s.γv (1 : Qp).half (wroteAtVs V gr rv) ∗ T s.owner q := by
  iintro ⟨#Hinv, #Hexcl, Hlc, #Hrec, Htok, Hg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  iunfold isRec at Hrec
  icases Hrec with ⟨#Hel, -⟩
  ihave %HR := ghost_map_lookup $$ Hrecs Hel
  iunfold pendTok at Htok
  ihave %HP := ghost_map_lookup $$ Hpend Htok
  have HR' : R !! r = some s := HR
  have HP' : P !! id = some ⟨r, gr, rv, q⟩ := HP
  obtain ⟨V0, hV0⟩ := Option.isSome_iff_exists.1 (Hwf.2.2.2.2.1 r (by simp [HR']))
  -- the record's mirror
  ihave Hv := (BigSepM.bigSepM_delete hV0).1 $$ Hvg
  icases Hv with ⟨⟨%s1, #Hel1, Hg1⟩, Hvg⟩
  ihave %Hs := ghostMapElem_agree $$ Hel Hel1
  subst Hs
  icombine Hg Hg1 gives % ⟨_, HV⟩
  subst HV
  -- the deposited permission
  ihave Hp := (BigSepM.bigSepM_delete HP').1 $$ Hptoks
  icases Hp with ⟨⟨%s2, #Hel2, HT⟩, Hptoks⟩
  ihave %Hs2 := ghostMapElem_agree $$ Hel Hel2
  subst Hs2
  -- no slot for the owner
  cases hE : E !! s.owner with
  | some e =>
    iexfalso
    iapply slot_excl T q hE $$ [$Hexcl $Hetoks $HT]
  | none =>
  have Hwf' := wf_withdraw Hwf HP' HR' hV0 hE
  imod ghostVar_update_halves (wroteAtVs V gr rv) $$ Hg Hg1 with ⟨Hg, Hg1⟩
  imod ghost_map_delete $$ Hpend Htok with Hpend
  imod Hclose $$ [HM HW Hrecs Hvg Hg1 Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists M, W, R, (<[r := wroteAtVs V gr rv]> Vg), (GMap.delete id P), n, E
    iframe; iframe #
    isplitl [Hvg Hg1]
    · iapply (BigSepM.bigSepM_insert_delete).2
      iframe Hvg
      iexists s; iframe #; iframe
    · ipureintro; exact Hwf'
  imodintro
  iframe

/-- **`EnsureReady` takes its slot** at its read of the map, which found `r` for `o`: its
permission `T o 1` is deposited, the slot holds `r`'s versions. -/
theorem ens_deposit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc} {o : Owner}
    {r : Loc} (qw : Qp) (hWo : W !! o = some r) :
    inv consN (consInv γ T) ∗ tokExcl T ∗ £ 1 ∗ ghostVar γ.W qw W ∗ T o 1 ⊢
      |={⊤}=> ghostVar γ.W qw W ∗ ∃ s V, isRec γ r s ∗ ⌜s.owner = o⌝ ∗ ensTok γ o ⟨r, V, false⟩ := by
  iintro ⟨#Hinv, #Hexcl, Hlc, HWg, HT⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  obtain ⟨s, hs, ho⟩ := owner_of_W Hwf hWo
  ihave #Hr := BigSepM.bigSepM_lookup hs $$ Hrecs_p
  obtain ⟨V, hV⟩ := Option.isSome_iff_exists.1 (Hwf.2.2.2.2.1 r (by simp [hs]))
  cases hE : E !! o with
  | some e =>
    iexfalso
    iapply slot_excl T 1 hE $$ [$Hexcl $Hetoks $HT]
  | none =>
  have Hwf' := wf_ens_deposit Hwf hWo hV hE
  imod ghost_map_insert o (⟨r, V, false⟩ : EnsSt) hE $$ Hens with ⟨Hens, Htok⟩
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks HT]
  · inext; iunfold consInv
    iexists M, W, R, Vg, P, n, (<[o := ⟨r, V, false⟩]> E)
    iframe; iframe #
    isplitl [Hetoks HT]
    · iapply (BigSepM.bigSepM_insert hE).2; iframe
    · ipureintro; exact Hwf'
  imodintro
  iframe HWg
  iexists s, V
  iframe Hr
  isplitr
  · ipureintro; exact ho
  · iunfold ensTok; iexact Htok

/-- Under the record's lock (its half of the record's mirror), the slot's versions are the
record's, and well formed. -/
theorem ens_agree (γ : ConsNames) (T : Owner → Qp → IProp GF) {o : Owner} {r : Loc} {s : RecS}
    {V : Vs} (b : Bool) (V' : Vs) :
    inv consN (consInv γ T) ∗ £ 1 ∗ ensTok γ o ⟨r, V, b⟩ ∗ isRec γ r s ∗
      ghostVar s.γv (1 : Qp).half V' ⊢
      |={⊤}=> ensTok γ o ⟨r, V, b⟩ ∗ ghostVar s.γv (1 : Qp).half V' ∗ ⌜V' = V ∧ vsWf V⌝ := by
  iintro ⟨#Hinv, Hlc, Htok, #Hrec, Hg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  iunfold ensTok at Htok
  ihave %HE := ghost_map_lookup $$ Hens Htok
  have HE' : E !! o = some ⟨r, V, b⟩ := HE
  obtain ⟨-, hV, -⟩ := Hwf.2.2.2.2.2 o _ HE'
  iunfold isRec at Hrec
  icases Hrec with ⟨#Hel, -⟩
  ihave Hv := (BigSepM.bigSepM_lookup_acc hV).1 $$ Hvg
  icases Hv with ⟨⟨%s1, #Hel1, Hg1⟩, Hvg⟩
  ihave %Hs := ghostMapElem_agree $$ Hel Hel1
  subst Hs
  icombine Hg Hg1 gives % ⟨_, HV⟩
  subst HV
  imod Hclose $$ [HM HW Hrecs Hvg Hg1 Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv; iexists M, W, R, Vg, P, n, E; iframe; iframe #
    isplitl [Hvg Hg1]
    · iapply Hvg; iexists s; iframe #; iframe
    · ipureintro; exact Hwf
  imodintro
  iunfold ensTok; iframe
  ipureintro; exact ⟨rfl, Hwf.2.2.2.1 _ _ hV⟩

/-- `EnsureReady`'s check of a record's versions `V`: what `readyRec` says of a record with them. -/
abbrev readyVs (S : GMap GR LastSyncRVGetter) (G : GR → GoString → IProp GF) (V : Vs) :
    IProp GF :=
  iprop([∗map] gr ↦ wroteRV ∈ V, ∃ readRV : GoString,
      □ G gr readRV ∗
      ⌜(∃ v, S !! gr = some v ∧ v ≠ interface.nil) ∧ readRV ≠ [] ∧
        (resourceversion.wellFormed readRV = true →
          resourceversion.decVal wroteRV ≤ resourceversion.decVal readRV)⌝)

/-- **`EnsureReady` finds its slot's versions ready** (its linearization point): the owner's
record is deleted abstractly (the slot is marked cleared), and what was checked holds of it. -/
theorem ens_ok_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) {o : Owner} {r : Loc} {s : RecS} {V : Vs}
    (K : Bool → IProp GF) :
    inv consN (consInv γ T) ∗ tokExcl T ∗ £ 1 ∗ £ 1 ∗ ensTok γ o ⟨r, V, false⟩ ∗ isRec γ r s ∗
      readyVs S G V ∗ auEns γ S G o K ⊢
      |={⊤}=> ensTok γ o ⟨r, V, true⟩ ∗ K true := by
  iintro ⟨#Hinv, #Hexcl, Hlc1, Hlc2, Htok, #Hrec, Hready, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  iunfold ensTok at Htok
  ihave %HE := ghost_map_lookup $$ Hens Htok
  have HE' : E !! o = some ⟨r, V, false⟩ := HE
  obtain ⟨-, -, s3, hs3, ho3⟩ := Hwf.2.2.2.2.2 o _ HE'
  -- no write to `r` is pending: it would hold a permission of `o`
  by_cases hex : ∃ id p, P !! id = some p ∧ p.r = r
  · obtain ⟨id, p, hp, hpr⟩ := hex
    iexfalso
    ihave Hp := BigSepM.bigSepM_lookup hp $$ Hptoks
    icases Hp with ⟨%s2, #Hel2, HT⟩
    rw [hpr] at *
    ihave %H2 := ghost_map_lookup $$ Hrecs Hel2
    have H2' : R !! r = some s2 := H2
    rw [hs3] at H2'; cases H2'
    rw [ho3]
    iapply slot_excl T p.q HE' $$ [$Hexcl $Hetoks $HT]
  have hnop : ∀ id p, P !! id = some p → p.r ≠ r := fun id p hp e => hex ⟨id, p, hp, e⟩
  obtain ⟨Hwf', hMo⟩ := wf_ens_ok Hwf HE' hnop
  imod lc_fupd_elim_later $$ Hlc2 HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  iunfold consState at HMc
  icombine HM HMc gives % ⟨_, HMeq⟩
  subst HMeq
  imod ghostVar_update_halves (GMap.delete o M) $$ HM HMc with ⟨HM, HMc⟩
  imod Hcl $$ %true [HMc Hready] with HK
  · iunfold consState
    simp only [↓reduceIte]
    iframe HMc
    rcases hMo with h | ⟨s1, -, h⟩
    · rw [h]; unfold readyRec; itrivial
    · rw [h]; unfold readyRec; iexact Hready
  imod ghost_map_update (⟨r, V, true⟩ : EnsSt) $$ Hens Htok with ⟨Hens, Htok⟩
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists (GMap.delete o M), W, R, Vg, P, n, (<[o := ⟨r, V, true⟩]> E)
    iframe; iframe #
    isplitl [Hetoks]
    · iapply (BigSepM.bigSepM_insert_delete).2
      iapply (BigSepM.bigSepM_delete HE').1 $$ Hetoks
    · ipureintro; exact Hwf'
  imodintro
  iframe HK
  iunfold ensTok; iexact Htok

/-- **`EnsureReady` finds them not ready**: it gives its slot up and takes its permission back;
the abstract state does not change. -/
theorem ens_err_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) {o : Owner} {r : Loc} {V : Vs} (K : Bool → IProp GF) :
    inv consN (consInv γ T) ∗ £ 1 ∗ £ 1 ∗ ensTok γ o ⟨r, V, false⟩ ∗ auEns γ S G o K ⊢
      |={⊤}=> T o 1 ∗ K false := by
  iintro ⟨#Hinv, Hlc1, Hlc2, Htok, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  iunfold ensTok at Htok
  ihave %HE := ghost_map_lookup $$ Hens Htok
  have HE' : E !! o = some ⟨r, V, false⟩ := HE
  have Hwf' := wf_ens_err Hwf HE' rfl
  imod lc_fupd_elim_later $$ Hlc2 HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  imod Hcl $$ %false [HMc] with HK
  · simp only [Bool.false_eq_true, ↓reduceIte]; iframe HMc
  imod ghost_map_delete $$ Hens Htok with Hens
  ihave ⟨HT, Hetoks⟩ := (BigSepM.bigSepM_delete HE').1 $$ Hetoks
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists M, W, R, Vg, P, n, (GMap.delete o E)
    iframe; iframe #
    ipureintro; exact Hwf'
  imodintro
  iframe

/-- `Clear(o, uid)`'s atomic update (for any caller but `EnsureReady`), closing into `K`. -/
abbrev auClear (γ : ConsNames) (o : Owner) (uid : GoString) (K : IProp GF) : IProp GF :=
  iprop(▷ |={⊤ \ ↑consN, ∅}=> ∃ M, consState γ M ∗
    (consState γ (clearM M o uid) -∗ |={∅, ⊤ \ ↑consN}=> K))

/-- Firing `Clear`'s atomic update on a state whose `clearM` is `M'`'s, and keeping the invariant's
half in step. -/
theorem fire_clear (γ : ConsNames) (M : GMap Owner Rec) (o : Owner) (uid : GoString) (K : IProp GF) :
    £ 1 ∗ ghostVar γ.M (1 : Qp).half M ∗ auClear γ o uid K ⊢
      |={⊤ \ ↑consN}=> ghostVar γ.M (1 : Qp).half (clearM M o uid) ∗ K := by
  iintro ⟨Hlc, HM, HAU⟩
  imod lc_fupd_elim_later $$ Hlc HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  iunfold consState at HMc
  icombine HM HMc gives % ⟨_, HMeq⟩
  subst HMeq
  imod ghostVar_update_halves (clearM M o uid) $$ HM HMc with ⟨HM, HMc⟩
  imod Hcl $$ [HMc] with HK
  · iunfold consState; iexact HMc
  imodintro
  iframe

/-- **`Clear` deletes the owner's record `r0`** (its UID matches, or `uid` is empty; the caller
holds the write lock's half of the map's mirror): its linearization point. -/
theorem clear_del_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {r0 : Loc} {s0 : RecS} {uid : GoString} (K : IProp GF)
    (hWo : W !! o = some r0) (hc : uid = [] ∨ s0.uid = uid) :
    inv consN (consInv γ T) ∗ £ 1 ∗ £ 1 ∗ ghostVar γ.W (1 : Qp).half W ∗ isRec γ r0 s0 ∗
      auClear γ o uid K ⊢
      |={⊤}=> ghostVar γ.W (1 : Qp).half (GMap.delete o W) ∗ K := by
  iintro ⟨#Hinv, Hlc1, Hlc2, HWg, #Hrec, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  iunfold isRec at Hrec
  icases Hrec with ⟨#Hel, -⟩
  ihave %HR := ghost_map_lookup $$ Hrecs Hel
  have Hwf' := wf_clear_del Hwf hWo HR hc
  imod fire_clear γ M o uid K $$ [$Hlc2 $HM $HAU] with ⟨HM, HK⟩
  imod ghostVar_update_halves (GMap.delete o W) $$ HWg HW with ⟨HWg, HW⟩
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists (clearM M o uid), (GMap.delete o W), R, Vg, P, n, E
    iframe; iframe #
    ipureintro; exact Hwf'
  imodintro
  iframe

/-- **`Clear` deletes nothing** (no record, or one for another UID with `uid` not empty): its
linearization point, the abstract state unchanged. -/
theorem clear_keep_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {uid : GoString} (qw : Qp) (K : IProp GF) :
    inv consN (consInv γ T) ∗ £ 1 ∗ £ 1 ∗ ghostVar γ.W qw W ∗
      (⌜W !! o = none⌝ ∨ ∃ r0 s0, ⌜W !! o = some r0 ∧ ¬ (uid = [] ∨ s0.uid = uid)⌝ ∗
        isRec γ r0 s0) ∗
      auClear γ o uid K ⊢
      |={⊤}=> ghostVar γ.W qw W ∗ K := by
  iintro ⟨#Hinv, Hlc1, Hlc2, HWg, Hk, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  ihave ⟨Hrecs, %hk⟩ : iprop(ghostMapAuth γ.recs 1 R ∗
      ⌜W !! o = none ∨ ∃ r0 s0, W !! o = some r0 ∧ R !! r0 = some s0 ∧
        ¬ (uid = [] ∨ s0.uid = uid)⌝) $$ [Hrecs Hk]
  · icases Hk with (%h | ⟨%r0, %s0, %h, #Hrec⟩)
    · iframe Hrecs; ipureintro; exact Or.inl h
    · iunfold isRec at Hrec
      icases Hrec with ⟨#Hel, -⟩
      ihave %HR := ghost_map_lookup $$ Hrecs Hel
      iframe Hrecs; ipureintro; exact Or.inr ⟨r0, s0, h.1, HR, h.2⟩
  have hM := clearM_keep Hwf hk
  imod fire_clear γ M o uid K $$ [$Hlc2 $HM $HAU] with ⟨HM, HK⟩
  rw [hM]
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists M, W, R, Vg, P, n, E
    iframe; iframe #
    ipureintro; exact Hwf
  imodintro
  iframe

/-- **`EnsureReady` finds no record** for the owner at its read of the map: its linearization
point; the owner has no abstract record, so `nil` (deleting it changes nothing). -/
theorem ens_none_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) {W : GMap Owner Loc} {o : Owner} (qw : Qp)
    (K : Bool → IProp GF) (hWo : W !! o = none) :
    inv consN (consInv γ T) ∗ £ 1 ∗ £ 1 ∗ ghostVar γ.W qw W ∗ auEns γ S G o K ⊢
      |={⊤}=> ghostVar γ.W qw W ∗ K true := by
  iintro ⟨#Hinv, Hlc1, Hlc2, HWg, HAU⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  have hMo : M !! o = none := by have h := Hwf.1 o; rw [hWo] at h; exact h
  imod lc_fupd_elim_later $$ Hlc2 HAU with HAU
  imod HAU with ⟨%M', HMc, Hcl⟩
  iunfold consState at HMc
  icombine HM HMc gives % ⟨_, HMeq⟩
  subst HMeq
  imod Hcl $$ %true [HMc] with HK
  · iunfold consState
    simp only [↓reduceIte, delete_none M o hMo, hMo]
    iframe HMc
    unfold readyRec; itrivial
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv; iexists M, W, R, Vg, P, n, E; iframe; iframe #
    ipureintro; exact Hwf
  imodintro
  iframe

/-- A record is registered once. -/
theorem isRec_agree (γ : ConsNames) {r : Loc} {s s' : RecS} :
    (isRec γ r s : IProp GF) ∗ isRec γ r s' ⊢ ⌜s = s'⌝ := by
  iintro ⟨H1, H2⟩
  iunfold isRec at H1 H2
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- Firing an atomic update that changes nothing (`Clear`'s, from `EnsureReady`). -/
theorem fire_trivial (K : IProp GF) :
    (|={⊤ \ ↑consN, ∅}=> ∃ _M : GMap Owner Rec, (True : IProp GF) ∗
      ((True : IProp GF) -∗ |={∅, ⊤ \ ↑consN}=> K)) ⊢ |={⊤}=> K := by
  iintro HAU
  imod (fupd_mask_subseteq (E1 := ⊤) (E2 := ⊤ \ ↑consN) (by simp)) with Hclose
  imod HAU with ⟨%M, -, Hcl⟩
  imod Hcl $$ %trivial with HK
  imod Hclose
  imodintro
  iexact HK

/-- `EnsureReady`'s own `Clear`: the map holds its slot's record or none for the owner. -/
theorem ens_clear_info (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {r : Loc} {V : Vs} (qw : Qp) :
    inv consN (consInv γ T) ∗ £ 1 ∗ ensTok γ o ⟨r, V, true⟩ ∗ ghostVar γ.W qw W ⊢
      |={⊤}=> ensTok γ o ⟨r, V, true⟩ ∗ ghostVar γ.W qw W ∗
        ⌜W !! o = some r ∨ W !! o = none⌝ := by
  iintro ⟨#Hinv, Hlc, Htok, HWg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  iunfold ensTok at Htok
  ihave %HE := ghost_map_lookup $$ Hens Htok
  have HE' : E !! o = some ⟨r, V, true⟩ := HE
  have hWo := (wf_clear_ens Hwf HE').2.2
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv; iexists M, W, R, Vg, P, n, E; iframe; iframe #
    ipureintro; exact Hwf
  imodintro
  iunfold ensTok; iframe
  ipureintro; exact hWo

/-- **`EnsureReady`'s own `Clear`** (under the write lock): the map loses the owner's record, if
any, the slot goes, and `EnsureReady` gets its permission back; the abstract state does not
change (the record was deleted abstractly already). -/
theorem ens_clear_commit (γ : ConsNames) (T : Owner → Qp → IProp GF) {W : GMap Owner Loc}
    {o : Owner} {r : Loc} {V : Vs} :
    inv consN (consInv γ T) ∗ £ 1 ∗ ensTok γ o ⟨r, V, true⟩ ∗ ghostVar γ.W (1 : Qp).half W ⊢
      |={⊤}=> ghostVar γ.W (1 : Qp).half (GMap.delete o W) ∗ T o 1 := by
  iintro ⟨#Hinv, Hlc, Htok, HWg⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iNamed Hi
  icombine HWg HW gives % ⟨_, HWeq⟩
  subst HWeq
  iunfold ensTok at Htok
  ihave %HE := ghost_map_lookup $$ Hens Htok
  have HE' : E !! o = some ⟨r, V, true⟩ := HE
  have Hwf' := (wf_clear_ens Hwf HE').1
  imod ghostVar_update_halves (GMap.delete o W) $$ HWg HW with ⟨HWg, HW⟩
  imod ghost_map_delete $$ Hens Htok with Hens
  ihave ⟨HT, Hetoks⟩ := (BigSepM.bigSepM_delete HE').1 $$ Hetoks
  imod Hclose $$ [HM HW Hrecs Hvg Hpend Hptoks Hens Hetoks]
  · inext; iunfold consInv
    iexists M, (GMap.delete o W), R, Vg, P, n, (GMap.delete o E)
    iframe; iframe #
    ipureintro; exact Hwf'
  imodintro
  iframe

end lemmas

end consistency
end EtcdGrove
end Perennial
