/-
Lean-first (no Rocq counterpart).

# k8setcd3: what `call` and `errOut` are stated with (stage 6f)

- `errIs err y`: `errOut(err)` is `y`: a `*StorageError` "not found" or "key exists" (its key and
  resource version), a callback's sentinel (`errDeleteRejected`, `errUpdateRejected`:
  `ERejected`), or any other error (`EOther`: not a `*StorageError` and neither sentinel).
- `unkErr_errIs`: an error of the store whose outcome is unknown (`unkErr`) is the last kind. For
  the client's errors that is a marked `sorry` (D30n): the client proof does not yet say its errors
  are not the driver's sentinels nor `*StorageError`s ("From the etcd client proof", item 5 of
  `notes/k8s-etcd3-plan.md`); an `InternalError` and the driver codec's (none) are proved.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.InvSteps

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
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
  iprop((∃ k rv, storageErrIs err (W64 1) k rv ∗ ⌜y = ⟨W64 1, k, rv, [], [], 0⟩⌝) ∨
    (∃ k rv, storageErrIs err (W64 2) k rv ∗ ⌜y = ⟨W64 2, k, rv, [], [], 0⟩⌝) ∨
    ((globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ err ∨
        globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ err) ∗
      ⌜y = rejectedL⌝) ∨
    (⌜y = errOutL⌝ ∗ ∃ eD eU : GoInterface,
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ∗
      ⌜ErrOther eD eU err⌝))

/-- **A client's error is not the driver's** (see the file header): a marked `sorry` (D30n) until
the client proof says what its errors are. -/
theorem clientErr_other (err eD eU : GoInterface) (_h : clientErr err) :
    globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ⊢
      (⌜ErrOther eD eU err⌝ : IProp GF) := by
  sorry

/-- **An error of the store whose outcome is unknown is `EOther`** (see the file header). -/
theorem unkErr_errIs (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ∗
      unkErr c err ⊢ errIs err errOutL := by
  iintro ⟨#Hpkg, #Hu⟩
  ihave #Hi : (github_com.mit_pdos.etcd_grove.examples.k8setcd3.drvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, -, ⟨%lD, #HD, -⟩, ⟨%lU, #HU, -⟩⟩
  iunfold errIs
  iright; iright; iright
  isplitr
  · ipureintro; rfl
  iexists _, _
  iframe HD HU
  iunfold unkErr at Hu
  icases Hu with ⟨%Hne, (⟨%Hc, -⟩ | %Hie)⟩
  · iapply clientErr_other err _ _ Hc
    iframe HD HU
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

/-- **Answers `call` places**: none of the errors of a resource version the driver does not ask
for (`rvSetOnCreate`, `tooLarge`). -/
def NoOddErr {E : Type} : KResp DObj E → Prop
  | .err .rvSetOnCreate => False
  | .err (.tooLarge _ _) => False
  | _ => True

/-- **`call`'s output of the store's answer** (see the file header): an error `errOut` places as
the answer's `outOf`, or the object `out` points to, whose `objOut` is it. -/
theorem respIs_call {E : Type} [KUserErr E] (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (r : KResp DObj E) (err out eD eU : GoInterface) (hodd : NoOddErr r)
    (hu : ∀ e err', r = .err (.user e) → KUserErr.is e err' → err' = eD ∨ err' = eU) :
    globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ∗
      respIs c r err out ⊢
      (⌜err ≠ GoInterface.nil⌝ ∗ errIs err (outOf r)) ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ (p : Loc) (o : Obj),
        ⌜out = interface.mkOk (go.GoType.PointerType objTyD) #p ∧ objOutL o = outOf r⌝ ∗ p ↦ o) := by
  iintro ⟨#HD, #HU, Hr⟩
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
      iright; iright; ileft
      isplitl
      · rcases hu e err rfl He.2 with h | h
        · rw [h]; ileft; iexact HD
        · rw [h]; iright; iexact HU
      ipureintro; rfl
    | rvSetOnCreate => exact hodd.elim
    | tooLarge _ _ => exact hodd.elim

theorem create_noOdd {E : Type} (s : KSt DObj) (k : GoString) (o : DObj) :
    NoOddErr (s.create (E := E) k o 0).2 := by
  unfold KSt.create
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  split <;> trivial

theorem get_noOdd {E : Type} (s : KSt DObj) (k : GoString) (ign : Bool) :
    NoOddErr (s.get (E := E) k 0 ign) := by
  unfold KSt.get
  simp only [gt_iff_lt, Nat.not_lt_zero, ↓reduceIte]
  split
  · trivial
  · split <;> trivial

theorem delete_noOdd (s : KSt DObj) (k : GoString) (eD : GoInterface) (r : GoString) :
    NoOddErr (s.delete k (fun _ _ => none) (rejD eD r)).2 := by
  unfold KSt.delete
  split
  · trivial
  · simp only
    split <;> trivial

theorem update_noOdd (s : KSt DObj) (k : GoString) (eU : GoInterface) (x : Input) :
    NoOddErr (s.update k false dzero (fun _ _ => none) (updD eU x)).2 := by
  unfold KSt.update
  repeat' split
  all_goals trivial

/-- A `Delete`'s callback error is `errDeleteRejected`'s value. -/
theorem delete_user (s : KSt DObj) (k : GoString) (eD : GoInterface) (r : GoString)
    (e : GoInterface) (h : (s.delete k (fun _ _ => none) (rejD eD r)).2 = .err (.user e)) :
    e = eD := by
  unfold KSt.delete at h
  split at h
  · cases h
  · simp only at h
    split at h
    · next e' he => simp only [rejD] at he; split at he <;> cases he; cases h; rfl
    · cases h

/-- An update's callback error is `errUpdateRejected`'s value. -/
theorem update_user (s : KSt DObj) (k : GoString) (eU : GoInterface) (x : Input)
    (e : GoInterface)
    (h : (s.update k false dzero (fun _ _ => none) (updD eU x)).2 = .err (.user e)) :
    e = eU := by
  unfold KSt.update at h
  split at h
  · cases h
  · simp only at h
    split at h
    · next e' he => simp only [updD] at he; split at he <;> cases he; cases h; rfl
    · split at h
      · split at h <;> cases h
      · cases h

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
      k8sAuRW sv.γr.kv c (delStep (mkeyL x.Key') (rejD eD x.Reject')) W Φ)
  else if x.Kind' = W64 2 then
    iprop(W ∗ [∗list] sv ∈ c.ms,
      k8sAuRW sv.γr.kv c (updStep (mkeyL x.Key') dzero (updD eU x)) W Φ)
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
    p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk o.1.1 o.1.2 n ⊢
      objAtD (GF := GF) (interface.mkOk (go.GoType.PointerType objTyD) #p) o (rvStr n) := by
  iintro H
  icases (typedPointsto_not_null_dup _ _ _) $$ H with ⟨H, %Hn⟩
  unfold objAtD
  iexists p, n
  iframe H
  ipureintro; exact ⟨rfl, Hn, rfl⟩

/-- **An input `Gen` may return**, as far as `Apply` needs: its name one of the workload's keys
(`workloadKeys`), its kind one of the four. -/
def GenIn (x : Input) : Prop :=
  (x.Key' = go!"a" ∨ x.Key' = go!"b" ∨ x.Key' = go!"c") ∧
    (x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ x.Kind' = W64 3)

/-- A sentinel's value (`errors.New`'s `*errorString`). -/
abbrev sentV (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #l

/-- `Apply`'s input (`lintest`'s `inOk`): a boxed `Input` `Gen` may return. -/
abbrev kInOk (i : GoInterface) : IProp GF := iprop(⌜∃ x, i = boxIn x ∧ GenIn x⌝)

/-- A workload key is one the store takes, under the driver's prefixes, and fits an object. -/
theorem genIn_ok (x : Input) (hx : GenIn x) :
    InOk x ∧ prepareKeyM go!"/objs" (storeKeyL x.Key') false = some (storeKeyL x.Key') ∧
      go!"/registry" ++ storeKeyL x.Key' = mkeyL x.Key' := by
  refine ⟨?_, ?_, rfl⟩
  · rcases hx.1 with h | h | h <;> (unfold InOk; rw [h]; decide)
  · rcases hx.1 with h | h | h <;> (rw [h]; decide)

/-- An answer `call` places is never `EOther`. -/
theorem outOf_err {E : Type} (r : KResp DObj E) (h : NoOddErr r) : (outOf r).Err' ≠ W64 4 := by
  cases r with
  | obj o rv => simp [outOf, objOutL]
  | zero => simp [outOf, zeroOutL]
  | err e =>
    cases e with
    | notFound k rv => simp [outOf]
    | keyExists k => simp [outOf]
    | user e => simp [outOf, rejectedL]
    | rvSetOnCreate => exact h.elim
    | tooLarge _ _ => exact h.elim

/-- **The store's model never answers `EOther`** (at any state). -/
theorem kStep_err (eD eU : GoInterface) (x : Input) (ks : KSt DObj) :
    (kStep eD eU x ks).2.Err' ≠ W64 4 := by
  unfold kStep
  by_cases h0 : x.Kind' = W64 0
  · rw [if_pos h0]; exact outOf_err _ (create_noOdd _ _ _)
  rw [if_neg h0]
  by_cases h1 : x.Kind' = W64 1
  · rw [if_pos h1]; exact outOf_err _ (delete_noOdd _ _ _ _)
  rw [if_neg h1]
  by_cases h2 : x.Kind' = W64 2
  · rw [if_pos h2]; exact outOf_err _ (update_noOdd _ _ _ _)
  rw [if_neg h2]
  exact outOf_err _ (get_noOdd _ _ _)

end defs

end k8setcd3
end EtcdGrove
end Perennial
