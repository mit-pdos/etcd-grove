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

/-- **`errOut(err)` is `y`** (see the file header). -/
def errIs (err : GoInterface) (y : Output) : IProp GF :=
  iprop((∃ k rv, storageErrIs err (W64 1) k rv ∗ ⌜y = ⟨W64 1, k, rv, [], [], [], 0⟩⌝) ∨
    (∃ k rv, storageErrIs err (W64 2) k rv ∗ ⌜y = ⟨W64 2, k, rv, [], [], [], 0⟩⌝) ∨
    (∃ k, invalidErrIs err k ∗ ⌜y = ⟨W64 5, k, 0, [], [], [], 0⟩⌝) ∨
    ((globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ err ∨
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ err) ∗
      ⌜y = rejectedL⌝) ∨
    (⌜y = errOutL⌝ ∗ ∃ eD eU : GoInterface,
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

/-- **An error of the store whose outcome is unknown is `EOther`** (see the file header). -/
theorem unkErr_errIs (hse : storageErrTyOk) (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      unkErr c err ⊢ errIs err errOutL := by
  iintro ⟨#Hpkg, #Hu⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, ⟨%lD, #HD, -, #CD⟩, ⟨%lU, #HU, -, #CU⟩⟩
  iunfold errIs
  iright; iright; iright; iright
  isplitr
  · ipureintro; rfl
  iexists _, _
  iframe HD HU
  iunfold unkErr at Hu
  icases Hu with ⟨%Hne, (⟨%Hc, -, #Hcl⟩ | %Hie)⟩
  · iapply clientErr_other hse err lD lU Hne Hc $$ Hcl CD CU
  · ipureintro
    rcases Hie with ⟨ie, rfl⟩ | he
    · have hne : ∀ t : go.GoType,
          k8s_io.apiserver.pkg.storage.InternalError.ty ≠ go.GoType.PointerType t := by
        intro t h
        rw [k8s_io.apiserver.pkg.storage.InternalError.ty] at h
        cases h
      refine ⟨fun h => ?_, fun h => ?_, _, rfl, hne _, fun h => absurd h (hne _)⟩
      · simp only [interface.mkOk, GoInterface.ok.injEq] at h
        exact hne _ (congrArg GoInterfaceOk.ty h)
      · simp only [interface.mkOk, GoInterface.ok.injEq] at h
        exact hne _ (congrArg GoInterfaceOk.ty h)
    · rw [hc] at he
      exact he.elim

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
      iright; iright; iright; ileft
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
      -- a `*StatusError`: neither sentinel (`eD`, `eU`: `errors.New`'s, by `drvInit`)
      unfold respIs
      icases Hr with ⟨%He, -⟩
      obtain ⟨l, rfl⟩ := He
      ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.drvInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      icases Hi with ⟨-, -, -, -, ⟨%lD, #HD', -, -⟩, ⟨%lU, #HU', -, -⟩⟩
      icombine HD HD' gives %hD
      icombine HU HU' gives %hU
      subst hD hU
      ileft
      isplitr
      · ipureintro; nofun
      iunfold errIs
      iright; iright; iright; iright
      isplitr
      · ipureintro; rfl
      iexists _, _
      iframe HD HU
      ipureintro
      have hse : k8s_io.apimachinery.pkg.api.errors.StatusError.ty ≠
          _root_.Perennial.errors.errorString.ty ∧
          k8s_io.apimachinery.pkg.api.errors.StatusError.ty ≠
            k8s_io.apiserver.pkg.storage.StorageError.ty := by
        unfold k8s_io.apimachinery.pkg.api.errors.StatusError.ty
          _root_.Perennial.errors.errorString.ty k8s_io.apiserver.pkg.storage.StorageError.ty
        refine ⟨?_, ?_⟩ <;> (intro h; injection h with h; simp at h)
      have hne : ∀ l' : Loc, interface.mkOk
          (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l ≠
          interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #l' := by
        intro l' h
        simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
        injection h.1 with h1
        exact hse.1 h1
      refine ⟨hne lD, hne lU, _, rfl, fun h => ?_, fun h => ?_⟩
      · injection h with h1; exact hse.2 h1
      · injection h with h1; exact absurd h1 hse.1

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
    (r : GoString) : NoOddErr (s.delete k pre (rejD eD r)).2 := by
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
    (r : GoString) (e : GoInterface) (h : (s.delete k pre (rejD eD r)).2 = .err (.user e)) :
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
      k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (preD x) (rejD eD x.Reject')) W Φ)
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

/-- A driver object in the heap is the store's object at its resource version's string. -/
theorem objAtD_pt (p : Loc) (o : DObj) (n : w64) :
    p ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk o.name o.uid o.val n ⊢
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
`d` (the comparisons unsigned, as Go's on `uint64`). -/
def minRVL (m d : w64) (c : Obj) (hasC : Bool) : GoString :=
  if m < 30 then []
  else if m < 45 then rvBytes 0
  else if m < 55 then rvBytes 1
  else if !hasC then []
  else if m < 84 then rvBytes c.ResourceVersion'
  else if m < 98 then (if c.ResourceVersion' ≤ d then rvBytes 1 else rvBytes (c.ResourceVersion' - d))
  else rvBytes (c.ResourceVersion' + d)

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
  (x.Key' = go!"a" ∨ x.Key' = go!"b" ∨ x.Key' = go!"c") ∧
    (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ x.Kind' = W64 3) ∧
    x.Val'.length ≤ 2 ^ 20 ∧ x.UID'.length < 256 ∧ (parseRVD x.MinRV').isSome ∧ CachedNoRV x

/-- A sentinel's value (`errors.New`'s `*errorString`). -/
abbrev sentV (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #l

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
  refine ⟨?_, ?_, rfl⟩
  · refine ⟨?_, hx.2.2.2.1, hx.2.2.2.2.1⟩
    rcases hx.1 with h | h | h <;> (rw [h]; decide)
  · rcases hx.1 with h | h | h <;> (rw [h]; decide)

/-- An answer `call` places is never `EOther`, but a too-large minimum resource version. -/
theorem outOf_err {E : Type} (r : KResp DObj E) (h : NoOddErr r)
    (ht : ∀ a b, r ≠ .err (.tooLarge a b)) : (outOf r).Err' ≠ W64 4 := by
  cases r with
  | obj o rv => simp [outOf, objOutL]
  | zero => simp [outOf, zeroOutL]
  | err e =>
    cases e with
    | notFound k rv => simp [outOf]
    | keyExists k => simp [outOf]
    | invalidObj k => simp [outOf]
    | user e => simp [outOf, rejectedL]
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
    refine outOf_err _ (delete_noOdd _ _ _ _ _) fun a b h => ?_
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
