/-
Lean-first (no Rocq counterpart).

# k8setcd3: what `call` and `errOut` are stated with (stage 6f)

- `errIs err y`: `errOut(err)` is `y`: a `*StorageError` "not found" or "key exists" (its key and
  resource version), a callback's sentinel (`errDeleteRejected`, `errUpdateRejected`:
  `ERejected`), or any other error (`EOther`: not a `*StorageError` and neither sentinel).
- `unkErr_errIs`: an error of the store whose outcome is unknown (`unkErr`) is the last kind: an
  `InternalError`, the driver codec's (none), or the client's (`clientErr_other`): the client's
  error is no caller's `errors.New` value (D37's `errCellOk`: the sentinels' cells hold the
  driver's messages, `errVarOk`), holds a pointer if it is an `*errorString` (`errCellOk_ptr`),
  and is a leaf error (`clientErr`), which `*StorageError` is not (its `Unwrap`, the method-set
  premise `storageErrTyOk`; "From the etcd client proof", item 5 of `notes/k8s-etcd3-plan.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.InvSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Cache

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The `*StorageError` type. -/
abbrev seTy : go.GoType :=
  go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty

/-- **An error `errOut` cannot place** (`EOther`): not a `*StorageError`, and neither of the
callbacks' sentinels (`eD`, `eU`, the variables' values); a `*errorString` (the sentinels' type,
compared by pointer) holds a pointer. -/
def ErrOther (eD eU err : GoInterface) : Prop :=
  err ≠ eD ∧ err ≠ eU ∧ ∃ ii : GoInterfaceOk, err = .ok ii ∧ ii.ty ≠ seTy ∧
    (ii.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ l : Loc, ii.v = #l)

/-- A sentinel's value (`errors.New`'s `*errorString`). -/
abbrev sentV (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #l

/-- **The client's errors are no `APIStatus`** (decision (A), etcd-grove-81, 2026-11-10; a lemma since
k8s 7e-1, `clientErrPlain_holds`, no longer a premise of the driver's specs):
the dynamic type of an error of etcd's client (`clientErr`) is outside `APIStatus`'s type set, so
`storage.IsTooLargeResourceVersion` (`errors.As` to `APIStatus`) does not recognize it. -/
def clientErrPlain : Prop :=
  ∀ ii : GoInterfaceOk, clientErr (GoInterface.ok ii) →
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false

/-- **`clientErrPlain` holds** (k8s 7e-1: `clientErr` fixes the dynamic type, `clientErrTys`): none
of the four types' method sets (`*status.Error`: `Error`, `GRPCStatus`, `Is`; `EtcdError`: `Code`,
`Error`; `*errorString`: `Error`; `deadlineExceededError`: `Error`, `Temporary`, `Timeout`) has
`APIStatus`'s `Status`. -/
theorem clientErrPlain_holds : clientErrPlain (sem := sem) := by
  intro ii hc
  have ht := ((hc.2 ii rfl).2).2
  simp only [clientErrTys, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht | ht | ht <;> rw [ht] <;> go_type_set

/-- **An error `IsTooLargeResourceVersion` does not recognize**: seen by it as a view (`apiErrAt`)
whose answer is `false`. -/
def notTooLarge (err : GoInterface) : IProp GF :=
  iprop(∃ w, apierrors.apiErrAt err w ∗ ⌜apierrors.tooLargeV w = false⌝)

instance notTooLarge_persistent (err : GoInterface) : Persistent (notTooLarge (GF := GF) err) := by
  unfold notTooLarge; infer_instance

/-- **`errOut(err)` is `y`** (see the file header; stage 7e-4: a too-large error, `ETooLarge`; an
`EOther` error is no too-large one, `notTooLarge`). -/
def errIs (err : GoInterface) (y : Output) : IProp GF :=
  iprop((∃ k rv, storageErrIs err (W64 1) k rv ∗ ⌜y = errOutL (W64 1) k rv⌝) ∨
    (∃ k rv, storageErrIs err (W64 2) k rv ∗ ⌜y = errOutL (W64 2) k rv⌝) ∨
    (∃ k, invalidErrIs err k ∗ ⌜y = errOutL (W64 5) k 0⌝) ∨
    (apierrors.tooLargeErrIs err ∗ ⌜y = tooLargeL⌝) ∨
    ((globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ err ∨
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ err) ∗
      ⌜y = rejectedL⌝) ∨
    (⌜y = otherL⌝ ∗ notTooLarge err ∗ ∃ eD eU : GoInterface,
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ eU ∗
      ⌜ErrOther eD eU err⌝))

/-- **A client's error is not the driver's** (see the file header): not the sentinels `errors.New`
made at `lD` and `lU` (their cells hold the driver's messages, none among the client's), not a
`*StorageError` (a leaf error, `*StorageError` has `Unwrap`: `storageErrTyOk`), and a pointer if
it is an `*errorString` (`errCellOk_ptr`). -/
theorem clientErr_other (hse : storageErrTyOk) (err : GoInterface) (lD lU : Loc)
    (hn : err ≠ GoInterface.nil) (hc : clientErr err) :
    go_etcd_io.etcd.cache.v3.errCellOk err ⊢
      EtcdGrove.errStrCell lD go!"k8setcd3: deletion rejected" -∗
      EtcdGrove.errStrCell lU go!"k8setcd3: update rejected" -∗
      (⌜ErrOther
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #lD)
        (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #lU)
        err⌝ : IProp GF) := by
  cases err with
  | nil => exact absurd rfl hn
  | ok ii =>
  iintro #Hcl #HD #HU
  iunfold EtcdGrove.errStrCell at HD HU
  ihave %HnD := go_etcd_io.etcd.cache.v3.errCellOk_ne _ lD _
    (by unfold go_etcd_io.etcd.cache.v3.clientErrMsgs; decide) $$ Hcl HD
  ihave %HnU := go_etcd_io.etcd.cache.v3.errCellOk_ne _ lU _
    (by unfold go_etcd_io.etcd.cache.v3.clientErrMsgs; decide) $$ Hcl HU
  ihave %Hp := go_etcd_io.etcd.cache.v3.errCellOk_ptr ii $$ Hcl
  ipureintro
  refine ⟨HnD, HnU, ii, rfl, fun ht => ?_, Hp⟩
  have hl := ((hc.2 ii rfl).1).2.1
  rw [ht] at hl
  exact hl hse

/-- **The package's sentinels** (`drvInit`): `errDeleteRejected`'s and `errUpdateRejected`'s
values, `errors.New`'s, their cells holding the driver's messages. -/
theorem drvInit_sents :
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) ⊢
      ∃ lD lU : Loc,
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ sentV lD ∗
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ sentV lU ∗
        EtcdGrove.errStrCell lD go!"k8setcd3: deletion rejected" ∗
        EtcdGrove.errStrCell lU go!"k8setcd3: update rejected" := by
  iintro ⟨-, -, -, HD, HU⟩
  iunfold github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk at HD
  iunfold github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk at HU
  icases HD with ⟨%lD, HD, -, CD⟩
  icases HU with ⟨%lU, HU, -, CU⟩
  iexists lD, lU
  iframe

/-- A client error is no too-large one (`clientErrPlain`, and `clientErr`'s leaf). -/
theorem clientErr_notTooLarge (err : GoInterface)
    (hn : err ≠ GoInterface.nil) (hc : clientErr err) : ⊢ notTooLarge (GF := GF) err := by
  cases err with
  | nil => exact absurd rfl hn
  | ok ii =>
  have hl := (hc.2 ii rfl).1
  iunfold notTooLarge
  iexists .plain
  unfold apierrors.apiErrAt
  ipureintro
  exact ⟨⟨ii, rfl, clientErrPlain_holds ii hc, hl.2.1, hl.2.2, hl.1⟩, rfl⟩

/-- **An error of the store whose outcome is unknown is `EOther`** (see the file header): the
client's (`clientErrPlain_holds`), not an `InternalError` (the driver's transformer never
fails: `trErr` is `False`) nor the codec's (none). -/
theorem unkErr_errIs (hse : storageErrTyOk) (c : StoreCfg GF DObj)
    (hc : c.S = driverSpec) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      unkErr c err ⊢ errIs err otherL := by
  iintro ⟨#Hpkg, #Hu⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%lD, %lU, #HD, #HU, #CD, #CU⟩ := drvInit_sents $$ Hi
  iunfold unkErr at Hu
  icases Hu with ⟨%Hne, (⟨%Hc, -, #Hcl⟩ | %Hie)⟩
  · iunfold errIs
    iright; iright; iright; iright; iright
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply clientErr_notTooLarge err Hne Hc
    iexists _, _
    iframe HD HU
    iapply clientErr_other hse err lD lU Hne Hc $$ Hcl CD CU
  · exfalso
    rcases Hie with ⟨ie, -, ht⟩ | he
    · rw [hc] at ht; exact ht.elim
    · rw [hc] at he; exact he.elim

/-- **A list's error is `EOther`** (`listErr`): the client's (`unkErr_errIs`), or the 410
`*StatusError` `interpretListError` makes, with no causes (so no too-large one), not a sentinel. -/
theorem listErr_errIs (hse : storageErrTyOk) (c : StoreCfg GF DObj)
    (hc : c.S = driverSpec) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      listErr c err ⊢ errIs err otherL := by
  iintro ⟨#Hpkg, #He⟩
  iunfold listErr at He
  icases He with (#Hu | ⟨%st, #Hw, %Hst⟩)
  · iapply unkErr_errIs hse c hc err
    iframe #
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave ⟨%lD, %lU, #HD, #HU, -, -⟩ := drvInit_sents $$ Hi
  iunfold errIs
  iright; iright; iright; iright; iright
  isplitr
  · ipureintro; rfl
  isplitr
  · iunfold notTooLarge
    iexists (apierrors.ApiErrView.status st [])
    isplitr
    · iexact Hw
    ipureintro
    simp [apierrors.tooLargeV, apierrors.causeIn]
  iexists _, _
  iframe HD HU
  iunfold apierrors.apiErrAt at Hw
  icases Hw with ⟨%l, %hl, -⟩
  ipureintro
  subst hl
  have hne : k8s_io.apimachinery.pkg.api.errors.StatusError.ty ≠ _root_.Perennial.errors.errorString.ty := by
    intro ht
    unfold k8s_io.apimachinery.pkg.api.errors.StatusError.ty _root_.Perennial.errors.errorString.ty at ht
    simp only [go.GoType.Named.injEq] at ht
    exact absurd ht.1 (by decide)
  refine ⟨?_, ?_, _, rfl, ?_, ?_⟩
  · simp [interface.mkOk, hne]
  · simp [interface.mkOk, hne]
  · intro ht
    simp only [seTy, go.GoType.PointerType.injEq] at ht
    unfold k8s_io.apimachinery.pkg.api.errors.StatusError.ty k8s_io.apiserver.pkg.storage.StorageError.ty at ht
    simp only [go.GoType.Named.injEq] at ht
    exact absurd ht.1 (by decide)
  · intro ht
    simp only [go.GoType.PointerType.injEq] at ht
    exact absurd ht hne

/-- A sentinel (`errors.New`'s `*errorString`) is seen as a plain error: no `APIStatus`, a leaf
(its method set is `Error` only). -/
theorem sentV_plain [_root_.Perennial.errors.Assumptions]
    [k8s_io.apimachinery.pkg.api.errors.Assumptions] (l : Loc) :
    ⊢ apierrors.apiErrAt (GF := GF) (sentV l) .plain := by
  have hU := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Unwrap"
  have hA := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"As"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hU hA
  unfold apierrors.apiErrAt
  ipureintro
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only
    go_type_set
  all_goals simp only [hU, hA, ne_eq, reduceCtorEq, not_false_eq_true]

theorem rvStr_inj {a b : w64} (h : rvStr a = rvStr b) : a = b := by
  have ha := parseRVD_rvStr a
  rw [h, parseRVD_rvStr b] at ha
  exact (Option.some.inj ha).symm

/-- **Answers `call` places**: not the error of a resource version set on a create (the driver
sets none). A `Get`'s too-large minimum resource version (stage 7b) is placed as `EOther`. -/
def NoOddErr {E : Type} : KResp DObj E → Prop
  | .err .rvSetOnCreate => False
  | _ => True

/-- **`call`'s output of the store's answer** (see the file header): an error `errOut` places as
the answer's `outOf`, or the object `out` points to, whose `objOut` is it. -/
theorem respIs_call {E : Type} [KUserErr E] (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (r : KResp DObj E) (err out eD eU : GoInterface) (hodd : NoOddErr r)
    (hu : ∀ e err', r = .err (.user e) → KUserErr.is e err' → err' = eD ∨ err' = eU) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ eU ∗
      respIs c r err out ⊢
      (⌜err ≠ GoInterface.nil⌝ ∗ errIs err (outOf r)) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
        ⌜out = interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = outOf r⌝ ∗ p ↦ o) := by
  iintro ⟨#Hpkg, #HD, #HU, Hr⟩
  cases r with
  | obj o rv =>
    unfold respIs
    rw [hc]
    icases Hr with ⟨%He, Hout⟩
    unfold driverSpec objAtD
    icases Hout with ⟨%p, %n, %Hp, Hp⟩
    obtain ⟨hout, -, hn⟩ := Hp
    have hn' : n = W64 (rv : Int) := (rvStr_inj hn).symm
    subst hn'
    iright
    isplitr
    · ipureintro; exact He
    iexists p, _
    iframe Hp
    ipureintro
    exact ⟨hout, rfl⟩
  | zero =>
    unfold respIs
    rw [hc]
    icases Hr with ⟨%He, Hout⟩
    unfold driverSpec objAtD
    icases Hout with ⟨%p, %n, %Hp, Hp⟩
    obtain ⟨hout, -, hn⟩ := Hp
    have hn' : n = 0 := rvStr_nil n hn.symm
    subst hn'
    iright
    isplitr
    · ipureintro; exact He
    iexists p, _
    iframe Hp
    ipureintro
    exact ⟨hout, rfl⟩
  | err e =>
    cases e with
    | notFound k rv =>
      unfold respIs
      icases Hr with ⟨Hse, -⟩
      iunfold storageErrIs at Hse
      icases Hse with ⟨%p, %He, #Hp⟩
      ileft
      isplitr
      · ipureintro; rw [He]; nofun
      iunfold errIs
      ileft
      iexists k, _
      isplitl
      · iunfold storageErrIs
        iexists p
        iframe Hp
        ipureintro; exact He
      ipureintro; rfl
    | keyExists k =>
      unfold respIs
      icases Hr with ⟨Hse, -⟩
      iunfold storageErrIs at Hse
      icases Hse with ⟨%p, %He, #Hp⟩
      ileft
      isplitr
      · ipureintro; rw [He]; nofun
      iunfold errIs
      iright; ileft
      iexists k, _
      isplitl
      · iunfold storageErrIs
        iexists p
        iframe Hp
        ipureintro; exact He
      ipureintro; rfl
    | user e =>
      unfold respIs
      icases Hr with ⟨%He, -⟩
      ileft
      isplitr
      · ipureintro; exact He.1
      iunfold errIs
      iright; iright; iright; iright; ileft
      isplitl
      · rcases hu e err rfl He.2 with h | h
        · rw [h]; ileft; iexact HD
        · rw [h]; iright; iexact HU
      ipureintro; rfl
    | rvSetOnCreate => exact hodd.elim
    | invalidObj k =>
      unfold respIs
      icases Hr with ⟨#Hse, -⟩
      ihave %Hne : ⌜err ≠ GoInterface.nil⌝ $$ [Hse]
      · iunfold invalidErrIs at Hse
        icases Hse with ⟨%l, %e, %He, -⟩
        ipureintro; rw [He]; nofun
      ileft
      isplitr
      · ipureintro; exact Hne
      iunfold errIs
      iright; iright; ileft
      iexists k
      iframe Hse
      ipureintro; rfl
    | tooLarge _ _ =>
      unfold respIs
      icases Hr with ⟨#Ht, -⟩
      ihave %Hp := apierrors.tooLargeErrIs_ptr err $$ Ht
      ileft
      isplitr
      · ipureintro; obtain ⟨l, rfl⟩ := Hp; nofun
      iunfold errIs
      iright; iright; iright; ileft
      iframe Ht
      ipureintro; rfl

theorem create_noOdd {E : Type} (s : KSt DObj) (k : GoString) (o : DObj) :
    NoOddErr (s.create (E := E) k o 0).2 := by
  unfold KSt.create
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  split <;> trivial

theorem get_noOdd {E : Type} (s : KSt DObj) (k : GoString) (n : Nat) (ign : Bool) :
    NoOddErr (s.get (E := E) k n ign) := by
  unfold KSt.get
  repeat' split
  all_goals trivial

theorem delete_noOdd (s : KSt DObj) (k : GoString) (pre : DObj → Nat → Bool) (eD : GoInterface)
    (b : Bool) (r : GoString) : NoOddErr (s.delete k pre (rejD eD b r)).2 := by
  unfold KSt.delete
  repeat' split
  all_goals trivial

theorem update_noOdd (s : KSt DObj) (k : GoString) (ign : Bool) (pre : DObj → Nat → Bool)
    (eU : GoInterface) (x : Input) : NoOddErr (s.update k ign dzero pre (updD eU x)).2 := by
  unfold KSt.update
  repeat' split
  all_goals trivial

/-- A `Delete`'s callback error is `errDeleteRejected`'s value. -/
theorem delete_user (s : KSt DObj) (k : GoString) (pre : DObj → Nat → Bool) (eD : GoInterface)
    (b : Bool) (r : GoString) (e : GoInterface)
    (h : (s.delete k pre (rejD eD b r)).2 = .err (.user e)) :
    e = eD := by
  unfold KSt.delete at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i he
  simp only [KResp.err.injEq, KErr.user.injEq] at h
  subst h
  unfold rejD at he
  split at he <;> simp_all

/-- An update's callback error is `errUpdateRejected`'s value. -/
theorem update_user (s : KSt DObj) (k : GoString) (ign : Bool) (pre : DObj → Nat → Bool)
    (eU : GoInterface) (x : Input) (e : GoInterface)
    (h : (s.update k ign dzero pre (updD eU x)).2 = .err (.user e)) :
    e = eU := by
  unfold KSt.update at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  rename_i he
  simp only [KResp.err.injEq, KErr.user.injEq] at h
  subst h
  unfold updD at he
  split at he <;> simp_all

/-- The store's step for a `Create` of `x`. -/
abbrev createStep (x : Input) : KSt DObj → KSt DObj :=
  fun s => (s.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1

/-- **What `call` needs for the input `x`** (by its kind): a `Create`'s one-shot updates, a
`Delete`'s or `GuaranteedUpdate`'s token and persistent updates, a `Get`'s maker of read
updates. -/
def callPre (c : StoreCfg GF DObj) (eD eU : GoInterface) (x : Input) (W : IProp GF)
    (Φ : KVState → IProp GF) (Q : w64 → w64 → KVState → IProp GF) : IProp GF :=
  if x.Kind' = W64 0 then iprop([∧list] sv ∈ c.ms, k8sAu1 sv.γr.kv c (createStep x) Φ)
  else if x.Kind' = W64 1 then
    iprop(W ∗ [∗list] sv ∈ c.ms,
      k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (preD x) (rejD eD x.HasReject' x.Reject')) W Φ)
  else if x.Kind' = W64 2 then
    iprop(W ∗ [∗list] sv ∈ c.ms,
      k8sAuRW sv.γr.kv c
        (updStep (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD eU x)) W Φ)
  else iprop(∀ R m, |==> □ [∧list] sv ∈ c.ms,
    ⌜Q R m = fun _ => iprop(True)⌝ ∨ kvReadAu sv.γr.kv (Q R m))

/-- **What the caller learns at the state `σ` the answer comes from**: its update's result (a
write), or the read's (a `Get`, at `σ`'s revision and the key's mod revision). -/
def callAt (x : Input) (Φ : KVState → IProp GF) (Q : w64 → w64 → KVState → IProp GF)
    (σ : KVState) : IProp GF :=
  if x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 then Φ σ
  else iprop(□ Q (W64 (σ.rev : Int)) (kubernetes.modAt (mkeyL x.Key') σ) σ)

/-- **What `call` needs for a list** (stage 7e-4; `store.GetList.spec`'s updates): the maker of the
first page's read updates `QL R` for the revision the client prophesies, and, from a first page's
result, its later pages' `PL σ`. -/
def listPre (c : StoreCfg GF DObj) (QL : w64 → KVState → IProp GF)
    (PL : KVState → KVState → IProp GF) : IProp GF :=
  iprop((∀ R, |==> □ [∧list] sv ∈ c.ms, ⌜QL R = fun _ => iprop(True)⌝ ∨ kvReadAu sv.γr.kv (QL R)) ∗
    (□ ∀ R σ, □ QL R σ -∗
      |==> □ [∧list] sv ∈ c.ms, ⌜PL σ = fun _ => iprop(True)⌝ ∨ kvReadAu sv.γr.kv (PL σ)))

/-- **`call`'s output at the state `σ`** (stage 7e-4): a list's `lOut`, else the store's model's. -/
def callOut (c : StoreCfg GF DObj) (eD eU : GoInterface) (x : Input) (σ : KVState) : Output :=
  if x.Kind' = W64 4 then lOut x σ else (kStep eD eU x (c.abs σ)).2

/-- A driver object in the heap is the store's object at its resource version's string. -/
theorem objAtD_pt (p : Loc) (o : DObj) (n : w64) :
    p ↦ o.toObj n ⊢
      objAtD (GF := GF) (interface.mkOk (go.GoType.PointerType objTyD) #p) o (rvStr n) := by
  iintro H
  icases (typedPointsto_not_null_dup _ _ _) $$ H with ⟨H, %Hn⟩
  unfold objAtD
  iexists p, n
  iframe H
  ipureintro; exact ⟨rfl, Hn, rfl⟩

/-- `uidOf(u)`: the UID a `Create` draws, `u`'s two low bytes. -/
def uidOfL (u : w64) : GoString := [u.extractLsb' 8 8, u.extractLsb' 0 8]

/-- `withPre(in, uid, rv, c, hasC)`: `in`'s preconditions from the cached object `c` (if any): its
UID if `uid`, its resource version's string if `rv`. -/
def withPreL (x : Input) (uid rv : Bool) (c : Obj) (hasC : Bool) : Input :=
  if hasC then
    { x with HasPreUID' := uid, PreUID' := if uid then c.UID' else x.PreUID',
             HasPreRV' := rv, PreRV' := if rv then rvStr c.ResourceVersion' else x.PreRV' }
  else x

/-- `minRV(m, d, c, hasC)`: a `Get`'s minimum resource version for the draw `m` and the offset
`d` (the comparisons unsigned, as Go's on `uint64`). Empty when the cached object's resource
version is at least `2 ^ 62` (the driver's bound, so that every string parses below `2 ^ 63`). -/
def minRVL (m d : w64) (c : Obj) (hasC : Bool) : GoString :=
  if m < 30 then []
  else if m < 45 then rvBytes 0
  else if m < 55 then rvBytes 1
  else if !hasC then []
  else if W64 (2 ^ 62) ≤ c.ResourceVersion' then []
  else if m < 84 then rvBytes c.ResourceVersion'
  else if m < 98 then (if c.ResourceVersion' ≤ d then rvBytes 1 else rvBytes (c.ResourceVersion' - d))
  else rvBytes (c.ResourceVersion' + d)

theorem parseRVD_rvBytes (n : w64) : parseRVD (rvBytes n) = some n := by
  have hb := bytesBE_rvBytes n
  simp only [rvBytes] at hb ⊢
  simp [parseRVD, hb]

/-- **Every string `minRV` returns parses below `2 ^ 63`** (`InOk`'s bound, from the driver's
`2 ^ 62` cut), for an offset `d` below `2 ^ 61` (the generator's are at most 200). -/
theorem minRVL_ok (m d : w64) (c : Obj) (hasC : Bool) (hd : uint.Z d ≤ 2 ^ 61) :
    ∃ k, parseRVD (minRVL m d c hasC) = some k ∧ uint.Z k < 2 ^ 63 := by
  unfold minRVL
  repeat' split
  all_goals first
    | exact ⟨0, rfl, by decide⟩
    | (refine ⟨_, parseRVD_rvBytes _, ?_⟩; word)

/-- **The cached object's scope premise** (D1 of stage 7b, `notes/k8s-etcd3-plan.md`;
`issues/k8s-etcd3-cached-noop-skips-preconditions.md`): an update with a cached object carries no
resource version precondition. -/
def CachedNoRV (x : Input) : Prop :=
  x.UseCached' = true → x.Kind' = W64 2 → x.HasPreRV' = false

/-- **An input `Gen` may return**, as far as `Apply` needs: its name one of the workload's keys
(`workloadKeys`), its kind one of the four, its value at most `2 ^ 20` bytes (an object it creates
or updates fits a request; 2026-10-31, `notes/invoke-size.md`, pass 4), its UID shorter than 256
bytes (`uidOf`'s two), its minimum resource version one `parseRV` takes (`minRV`'s), and no
resource version precondition on an update with a cached object (`CachedNoRV`). -/
def GenIn (x : Input) : Prop :=
  InOk x ∧ (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ x.Kind' = W64 3 ∨ x.Kind' = W64 4) ∧
    x.Val'.length ≤ 2 ^ 20 ∧ CachedNoRV x


/-- `Apply`'s input (`lintest`'s `inOk`): a boxed `Input` `Gen` may return, with its cached object
one of the store `c` (`cachedIn`). -/
def kInOk (c : StoreCfg GF DObj) (i : GoInterface) : IProp GF :=
  iprop(∃ x, ⌜i = boxIn x ∧ GenIn x⌝ ∗ cachedIn c x)

instance kInOk_persistent (c : StoreCfg GF DObj) (i : GoInterface) :
    Persistent (kInOk (GF := GF) c i) := by
  unfold kInOk; infer_instance

/-- A workload key is one the store takes, under the driver's prefixes, and fits an object. -/
theorem genIn_ok (x : Input) (hx : GenIn x) :
    InOk x ∧ prepareKeyM go!"/objs" (storeKeyL x.Key') false = some (storeKeyL x.Key') ∧
      go!"/registry" ++ storeKeyL x.Key' = mkeyL x.Key' := by
  refine ⟨hx.1, ?_, rfl⟩
  have hk := hx.1.1
  simp only [wkKeysL, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h | h <;> (rw [h]; decide)

/-- An answer `call` places is never `EOther`, but a too-large minimum resource version. -/
theorem outOf_err {E : Type} (r : KResp DObj E) (h : NoOddErr r)
    (ht : ∀ a b, r ≠ .err (.tooLarge a b)) : (outOf r).Err' ≠ W64 4 := by
  cases r with
  | obj o rv => simp [outOf, objOutL]
  | zero => simp [outOf, zeroOutL, errOutL]
  | err e =>
    cases e with
    | notFound k rv => simp [outOf, errOutL]
    | keyExists k => simp [outOf, errOutL]
    | invalidObj k => simp [outOf, errOutL]
    | user e => simp [outOf, rejectedL, errOutL]
    | rvSetOnCreate => exact h.elim
    | tooLarge a b => exact absurd rfl (ht a b)

/-- **The store's model never answers `EOther`** (at any state), but to a `Get` whose minimum
resource version is above the state's (stage 7b: too large). -/
theorem kStep_err (eD eU : GoInterface) (x : Input) (ks : KSt DObj)
    (hk : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ uint.nat (minOf x) ≤ ks.rv) :
    (kStep eD eU x ks).2.Err' ≠ W64 4 := by
  unfold kStep
  by_cases h0 : x.Kind' = W64 0
  · rw [ite_eq_left h0]
    refine outOf_err _ (create_noOdd _ _ _) fun a b h => ?_
    unfold KSt.create at h
    repeat' split at h
    all_goals cases h
  rw [ite_eq_right h0]
  by_cases h1 : x.Kind' = W64 1
  · rw [ite_eq_left h1]
    refine outOf_err _ (delete_noOdd _ _ _ _ _ _) fun a b h => ?_
    unfold KSt.delete at h
    repeat' split at h
    all_goals cases h
  rw [ite_eq_right h1]
  by_cases h2 : x.Kind' = W64 2
  · rw [ite_eq_left h2]
    refine outOf_err _ (update_noOdd _ _ _ _ _ _) fun a b h => ?_
    unfold KSt.update at h
    repeat' split at h
    all_goals cases h
  rw [ite_eq_right h2]
  have hmin : uint.nat (minOf x) ≤ ks.rv := by
    rcases hk with h | h | h | h
    · exact absurd h h0
    · exact absurd h h1
    · exact absurd h h2
    · exact h
  refine outOf_err _ (get_noOdd _ _ _ _) fun a b h => ?_
  unfold KSt.get at h
  rw [if_neg (by omega)] at h
  repeat' split at h
  all_goals cases h

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
