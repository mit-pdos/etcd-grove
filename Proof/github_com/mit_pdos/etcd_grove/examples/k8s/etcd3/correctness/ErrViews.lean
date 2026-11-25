/-
Lean-first (no Rocq counterpart).

# The checker's error tests on a `Response.Err` (k8s 7g step 3)

`validateGet`, `validateList` and `Step` ask of a response's error `storage.IsNotFound`,
`storage.IsTooLargeResourceVersion` and `apierrors.SuggestsClientDelay`. Their specs read the
error through `k8s.errCodeAt` and `apierrors.apiErrAt`/`apiErrOk`; this file gives those views of
an `errRep` whose error is **flat** (`flatE`): `nil`, an `errors.New` error, a `*StorageError`
wrapping `nil` or an `errors.New` error (every deep error the model and the store make), or
storage's too-large error. `RErr.other` has no view (`Step`'s premise excludes it).

- `codeE e`: the `*StorageError` code (`errRep_codeAt`); `isNotFoundE` is `codeE e = some 1`.
- `errRep_apiErrAt`: a view `w` with `tooLargeV w = isTooLargeE e` (`.plain` for a flat deep error,
  a `*StorageError` being a one-level wrapper whose `Unwrap` returns a leaf; the too-large error's
  status).
- `wp_DeepEqual_resp`: `reflect.DeepEqual(expected, output)` is `respEqL` when the expected error
  is a deep one (clause 2 of `reflect.DeepEqual.spec_k8s`, or clause 4 for the output's too-large
  error).
- `errRep_apiErrOk`, `errRep_delay`: `SuggestsClientDelay`'s precondition, and its answer is
  `delayE e`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs
public import Proof.k8s_io.apiserver.pkg.storage.ErrCode
public import Spec.k8s_io.apiserver.pkg.storage.StorageError__Unwrap
public import Spec.reflect.DeepEqualK8s

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section pure
variable [GooseExts]

/-- **A flat deep error** (see the file header). -/
def flatD : DeepV → Prop
  | .nil => True
  | .errString _ => True
  | .storageErr _ _ _ .nil => True
  | .storageErr _ _ _ (.errString _) => True
  | _ => False

/-- **An error the checker's tests take** (see the file header). -/
def flatE : RErr → Prop
  | .deep d => flatD d
  | .tooLarge _ => True
  | .other => False

/-- A `*StorageError`'s code. -/
def codeE : RErr → Option w64
  | .deep (.storageErr c _ _ _) => some c
  | _ => none

/-- **A `Get`'s output object**: nil or an object (the versioner's `ObjectResourceVersion` takes
the driver's `*Obj`). -/
def objOrNilD : DeepV → Prop
  | .nil => True
  | .obj _ => True
  | _ => False

theorem isNotFoundE_codeE (e : RErr) : isNotFoundE e = decide (codeE e = some (W64 1)) := by
  unfold isNotFoundE codeE
  rcases e with d | _ | _
  · cases d <;> simp
  · simp
  · simp

theorem errNonNil_false (e : RErr) (h : errNonNil e = false) : e = .deep .nil := by
  rcases e with d | _ | _ <;> simp [errNonNil] at h
  cases d <;> simp at h ⊢

theorem notFound_nonNil (e : RErr) (h : isNotFoundE e = true) : errNonNil e = true := by
  rcases e with d | _ | _ <;> simp [isNotFoundE] at h
  cases d <;> simp at h ⊢
  rfl

theorem notFound_shape (e : RErr) (h : isNotFoundE e = true) :
    ∃ k r i, e = .deep (.storageErr (W64 1) k r i) := by
  rcases e with d | _ | _ <;> simp [isNotFoundE] at h
  cases d <;> simp at h ⊢
  exact h

/-! The model's responses (`rexecL`): flat errors, nil-or-list objects for a list. -/

/-- **A deep error the model makes** (create, update, delete, get): flat and deep. -/
def modelDeepE (m : RM) (key : GoString) (e : RErr) : Prop :=
  e = .none ∨ e = existsE m key ∨ e = notFoundE m key ∨ (∃ msg, e = invalidE m key msg) ∨
    e = updRejE ∨ e = delRejE

theorem modelDeepE_flat (m : RM) (key : GoString) (e : RErr) (h : modelDeepE m key e) :
    flatE e ∧ deepErrE e := by
  rcases h with rfl | rfl | rfl | ⟨msg, rfl⟩ | rfl | rfl <;> exact ⟨trivial, trivial⟩

theorem rcreateL_err (x : Input) (m : RM) :
    (rcreateL x m).1.err = .other ∨ modelDeepE m (k8s_etcd3.storeKeyL x.Key') (rcreateL x m).1.err := by
  unfold rcreateL failR modelDeepE; dsimp only; (repeat' split) <;> simp

theorem rdeleteL_err (x : Input) (m : RM) :
    (rdeleteL x m).1.err = .other ∨ modelDeepE m (k8s_etcd3.storeKeyL x.Key') (rdeleteL x m).1.err := by
  unfold rdeleteL failR modelDeepE; dsimp only; (repeat' split) <;> first | (simp; done) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))

theorem rupdateL_err (x : Input) (m : RM) :
    (rupdateL x m).1.err = .other ∨ modelDeepE m (k8s_etcd3.storeKeyL x.Key') (rupdateL x m).1.err := by
  unfold rupdateL failR updWriteL modelDeepE; dsimp only; (repeat' split) <;> first | (simp; done) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))

theorem rgetL_err (x : Input) (m : RM) :
    (rgetL x m).err = .other ∨ (rgetL x m).err = tooLargeE ∨
      modelDeepE m (k8s_etcd3.storeKeyL x.Key') (rgetL x m).err := by
  unfold rgetL modelDeepE; dsimp only; (repeat' split) <;> simp

theorem rlistL_err (x : Input) (m : RM) :
    (rlistL x m).err = .other ∨ (rlistL x m).err = tooLargeE ∨ (rlistL x m).err = .none := by
  unfold rlistL; dsimp only; (repeat' split) <;> simp

theorem rexecL_flat (x : Input) (m : RM) (h : (rexecL x m).1.err ≠ .other) :
    flatE (rexecL x m).1.err := by
  unfold rexecL at h ⊢
  by_cases k4 : x.Kind' = W64 4
  · simp only [k4, ↓reduceIte] at h ⊢
    rcases rlistL_err x m with e | e | e
    · exact absurd e h
    · rw [e]; trivial
    · rw [e]; trivial
  by_cases k0 : x.Kind' = W64 0
  · simp only [k4, k0, ↓reduceIte] at h ⊢
    rcases rcreateL_err x m with e | e
    · exact absurd e h
    · exact (modelDeepE_flat _ _ _ e).1
  by_cases k1 : x.Kind' = W64 1
  · simp only [k4, k0, k1, ↓reduceIte] at h ⊢
    rcases rdeleteL_err x m with e | e
    · exact absurd e h
    · exact (modelDeepE_flat _ _ _ e).1
  by_cases k2 : x.Kind' = W64 2
  · simp only [k4, k0, k1, k2, ↓reduceIte] at h ⊢
    rcases rupdateL_err x m with e | e
    · exact absurd e h
    · exact (modelDeepE_flat _ _ _ e).1
  · simp only [k4, k0, k1, k2, ↓reduceIte] at h ⊢
    rcases rgetL_err x m with e | e | e
    · exact absurd e h
    · rw [e]; trivial
    · exact (modelDeepE_flat _ _ _ e).1

theorem rexecL_write_deep (x : Input) (m : RM) (hw : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2)
    (h : (rexecL x m).1.err ≠ .other) : deepErrE (rexecL x m).1.err := by
  have h4 : x.Kind' ≠ W64 4 := by rcases hw with e | e | e <;> rw [e] <;> decide
  unfold rexecL at h ⊢
  by_cases k0 : x.Kind' = W64 0
  · simp only [h4, k0, ↓reduceIte] at h ⊢
    rcases rcreateL_err x m with e | e
    · exact absurd e h
    · exact (modelDeepE_flat _ _ _ e).2
  by_cases k1 : x.Kind' = W64 1
  · simp only [h4, k0, k1, ↓reduceIte] at h ⊢
    rcases rdeleteL_err x m with e | e
    · exact absurd e h
    · exact (modelDeepE_flat _ _ _ e).2
  have k2 : x.Kind' = W64 2 := by rcases hw with e | e | e <;> simp_all
  simp only [h4, k0, k1, k2, ↓reduceIte] at h ⊢
  rcases rupdateL_err x m with e | e
  · exact absurd e h
  · exact (modelDeepE_flat _ _ _ e).2

theorem rlistL_listOrNil (x : Input) (m : RM) : listOrNilD (rlistL x m).obj := by
  unfold rlistL; dsimp only
  (repeat' split) <;> simp [listOrNilD]

end pure

section views
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
variable [apierrors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem errorString_ne_storageError :
    _root_.Perennial.errors.errorString.ty ≠ k8s_io.apiserver.pkg.storage.StorageError.ty := by
  intro ht
  unfold k8s_io.apiserver.pkg.storage.StorageError.ty _root_.Perennial.errors.errorString.ty at ht
  simp only [go.GoType.Named.injEq] at ht
  exact absurd ht.1 (by decide)

theorem statusError_ne_storageError :
    k8s_io.apimachinery.pkg.api.errors.StatusError.ty ≠ k8s_io.apiserver.pkg.storage.StorageError.ty := by
  intro ht
  unfold k8s_io.apiserver.pkg.storage.StorageError.ty k8s_io.apimachinery.pkg.api.errors.StatusError.ty at ht
  simp only [go.GoType.Named.injEq] at ht
  exact absurd ht.1 (by decide)

/-- **The `*StorageError` code of a flat error.** -/
theorem errRep_codeAt (x : GoInterface) (e : RErr) (hf : flatE e) :
    errRep (GF := GF) x e ⊢ k8s.errCodeAt x DFrac.discard (codeE e) := by
  rcases e with d | dl | _
  · cases d with
    | nil =>
      simp only [errRep, deepRO, deepRep, codeE, k8s.errCodeAt]
      iintro %h
      ipureintro; left; exact h
    | errString s =>
      simp only [errRep, deepRO, deepRep, codeE, k8s.errCodeAt]
      iintro ⟨%p, %h, -⟩
      ipureintro; right
      subst h
      refine ⟨_, rfl, ?_⟩
      simpa using errorString_ne_storageError
    | storageErr c k rv inner =>
      simp only [errRep, deepRO, deepRep, codeE, k8s.errCodeAt]
      iintro ⟨%p, %ie, %h, #Hp, -⟩
      iexists p, _
      iframe Hp
      ipureintro; exact ⟨h, rfl⟩
    | obj _ | list _ _ _ _ => exact hf.elim
  · simp only [errRep, codeE, k8s.errCodeAt]
    iintro ⟨#Ht, -⟩
    ihave %Hp := apierrors.tooLargeErrIs_ptr x $$ Ht
    obtain ⟨l, rfl⟩ := Hp
    ipureintro; right
    refine ⟨_, rfl, ?_⟩
    simpa using statusError_ne_storageError
  · exact hf.elim

/-- `errors.New`'s error is a leaf outside `APIStatus` (its method set is `Error` only). -/
theorem errString_plainLeaf (p : Loc) :
    apierrors.plainLeaf (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #p) := by
  have hU := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Unwrap"
  have hA := go.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"As"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hU hA
  refine Or.inr ⟨_, rfl, ?_, ⟨?_, ?_, ?_⟩, ⟨_, p, rfl, rfl⟩⟩
  · simp only
    go_type_set
  all_goals simp only [hU, hA, ne_eq, reduceCtorEq, not_false_eq_true]

/-- **A flat deep error is seen as `.plain`**: `nil`, a leaf (`errors.New`'s), or a `*StorageError`,
a one-level wrapper (not in `APIStatus`'s type set, `Unwrap() error`, no `As`) whose `Unwrap`
returns its inner error, `nil` or a leaf. -/
theorem deepRO_plain (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG))
    (x : GoInterface) (d : DeepV) (hf : flatD d) :
    deepRO (GF := GF) x d ⊢ apierrors.apiErrAt x .plain := by
  cases d with
  | nil =>
    simp only [deepRO, deepRep, apierrors.apiErrAt]
    iintro %h
    ileft; ipureintro; left; exact h
  | errString s =>
    simp only [deepRO, deepRep, apierrors.apiErrAt]
    iintro ⟨%p, %h, -⟩
    ileft; ipureintro; subst h; exact errString_plainLeaf p
  | storageErr c k rv inner =>
    have hinner : ∀ e, (deepRO (GF := GF) e inner ⊢ ⌜apierrors.plainLeaf e⌝) := by
      intro e
      cases inner with
      | nil => simp only [deepRO, deepRep]; iintro %h; ipureintro; left; exact h
      | errString s =>
        simp only [deepRO, deepRep]
        iintro ⟨%p, %h, -⟩
        ipureintro; subst h; exact errString_plainLeaf p
      | _ => exact hf.elim
    simp only [deepRO, deepRep, apierrors.apiErrAt]
    iintro ⟨%p, %ie, %h, #Hp, #Hi⟩
    ihave %Hl := hinner ie $$ Hi
    subst h
    iright
    have hU := go.method_set_is
      (t := go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) go!"Unwrap"
    have hA := go.method_set_is
      (t := go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) go!"As"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hU hA
    iexists _
    isplitr
    · ipureintro
      refine ⟨rfl, ?_, hU, ?_, ⟨_, p, rfl, rfl⟩⟩
      · simp only
        go_type_set
      · simp only [hA, ne_eq, reduceCtorEq, not_false_eq_true]
    imodintro
    iintro %Φ HΦ
    wp_apply wp_Unwrap p DFrac.discard _ $$ [$Hp] as -
    iapply HΦ
    ipureintro; exact Hl
  | obj _ | list _ _ _ _ => exact hf.elim

/-- **A view of a flat error that `IsTooLargeResourceVersion` answers `isTooLargeE` on.** -/
theorem errRep_apiErrAt (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG))
    (x : GoInterface) (e : RErr) (hf : flatE e) :
    errRep (GF := GF) x e ⊢ ∃ w, apierrors.apiErrAt x w ∗ ⌜apierrors.tooLargeV w = isTooLargeE e⌝ := by
  rcases e with d | dl | _
  · simp only [errRep]
    iintro #H
    iexists .plain
    isplitl
    · iapply deepRO_plain wp_Unwrap x d hf $$ H
    · ipureintro; rfl
  · simp only [errRep, apierrors.tooLargeErrIs]
    iintro ⟨⟨%st, %cs, #Ha, %hst, -⟩, -⟩
    iexists .status st cs
    iframe Ha
    ipureintro
    simp [apierrors.tooLargeV, apierrors.timeoutV, apierrors.causeIn, isTooLargeE, hst.1, hst.2]
  · exact hf.elim

/-- **A flat error is one `apierrors`' checks may read** (`apiErrOk`). -/
theorem errRep_apiErrOk (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG))
    (x : GoInterface) (e : RErr) (hf : flatE e) :
    errRep (GF := GF) x e ⊢ apierrors.apiErrOk x := by
  unfold apierrors.apiErrOk
  rcases e with d | dl | _
  · simp only [errRep]
    iintro #H
    iright
    iapply deepRO_plain wp_Unwrap x d hf $$ H
  · simp only [errRep, apierrors.tooLargeErrIs, apierrors.apiErrAt]
    iintro ⟨⟨%st, %cs, ⟨%l, %h, #Hl, #Hd⟩, -, -⟩, -⟩
    ileft
    iexists l, st
    iframe Hl
    isplitr
    · ipureintro; exact h
    iexists cs
    iexact Hd
  · exact hf.elim

/-- **`SuggestsClientDelay`'s answer on a flat error is `delayE`** (its post, on the error's
view: `.plain` for a deep error; the too-large error's status, whose details `errRep` holds). -/
theorem errRep_delay (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG))
    (x : GoInterface) (e : RErr) (hf : flatE e) (n : w64) (b : Bool) :
    errRep (GF := GF) x e ∗ (□ ∀ w, apierrors.apiErrAt x w -∗
      match w with
      | .plain => ⌜n = W64 0 ∧ b = false⌝
      | .status st _ => ⌜st.Details' = null ∧ n = W64 0 ∧ b = false⌝ ∨
          ∃ d, ⌜st.Details' ≠ null⌝ ∗ st.Details' ↦□ d ∗ ⌜(n, b) = apierrors.delayV st d⌝) ⊢
    ⌜b = delayE e⌝ := by
  rcases e with d | dl | _
  · iintro ⟨#H, #Hq⟩
    simp only [errRep]
    ihave #Hp := deepRO_plain wp_Unwrap x d hf $$ H
    ihave %Hr := Hq $$ Hp
    ipureintro; simp [delayE, Hr.2]
  · simp only [errRep, apierrors.tooLargeErrIs, apierrors.apiErrAt]
    iintro ⟨⟨⟨%st, %cs, ⟨%l, %h, #Hl, #Hds⟩, -, -⟩, %l', %st', %dv, ⟨%h', -, %hd⟩, #Hl', #Hdv⟩, #Hq⟩
    rw [h] at h'
    have hll : l = l' := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h'
      exact GoGlobalContext.intoVal_inj_loc h'
    subst hll
    icombine Hl Hl' gives %Hst
    simp only [k8s_io.apimachinery.pkg.api.errors.StatusError.mk.injEq] at Hst
    subst Hst
    ihave Hr := Hq $$ %(.status st cs)
    ihave Hr := Hr $$ [Hds]
    · iexists l
      iframe Hl Hds
      ipureintro; exact h
    isimp only at Hr
    icases Hr with (%Hr | ⟨%d, %hn, #Hd, %Hr⟩)
    · obtain ⟨hn, -, -⟩ := Hr
      icases (typedPointsto_not_null_dup _ _ _) $$ Hdv with ⟨-, %Hnn⟩
      exact absurd hn Hnn
    · icombine Hd Hdv gives %Hdd
      subst Hdd
      ipureintro
      rw [delayE, ← hd]
      exact (congrArg Prod.snd Hr)
  · exact hf.elim

/-- **`reflect.DeepEqual` of two `Response`s is `respEqL`**, for an expected error with a deep view
and a flat output error: clause 2 of `reflect.DeepEqual.spec_k8s` (two deep errors), clause 4 (the
output's too-large error, `false`). -/
theorem wp_DeepEqual_resp (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (o1 e1 o2 e2 : GoInterface) (eo oo : DeepV) (ee oe : RErr)
    (hee : deepErrE ee) (hoe : flatE oe) :
    {{ deepRO (GF := GF) o1 eo ∗ errRep e1 ee ∗ deepRO o2 oo ∗ errRep e2 oe }}
      (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o1 e1))))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o2 e2))))
    {{ RET #(respEqL ⟨eo, ee⟩ ⟨oo, oe⟩); True }} := by
  rcases ee with d1 | _ | _
  · rcases oe with d2 | dl | _
    · iintro %Φ ⟨#Ho1, #He1, #Ho2, #He2⟩ HΦ
      simp only [errRep]
      wp_apply (wp_DE.2.1 o1 e1 o2 e2 eo d1 oo d2 DFrac.discard DFrac.discard) $$ [] as %b ⟨%hb, -⟩
      · iframe Ho1 He1 Ho2 He2
      have : b = respEqL ⟨eo, .deep d1⟩ ⟨oo, .deep d2⟩ := by
        unfold respEqL
        cases b <;> simp_all
      rw [this]
      iapply HΦ; itrivial
    · iintro %Φ ⟨#Ho1, #He1, #Ho2, #He2⟩ HΦ
      simp only [errRep]
      icases He2 with ⟨#Ht, -⟩
      ihave %Hp := apierrors.tooLargeErrIs_ptr e2 $$ Ht
      obtain ⟨l, rfl⟩ := Hp
      wp_apply (wp_DE.2.2.2 o1 e1 o2 l eo d1 oo DFrac.discard DFrac.discard) $$ [] as %b ⟨%hb, -⟩
      · iframe Ho1 He1 Ho2
      subst hb
      rw [show respEqL ⟨eo, .deep d1⟩ ⟨oo, .tooLarge dl⟩ = false from rfl]
      iapply HΦ; itrivial
    · exact hoe.elim
  · exact hee.elim
  · exact hee.elim

/-- **`IsTooManyRequests` answers `false` on a flat error** (its post, on the error's view: `.plain`
for a deep error; the too-large error's status, reason `Timeout` and code 504). -/
theorem errRep_notTooMany (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG))
    (x : GoInterface) (e : RErr) (hf : flatE e) (b : Bool) :
    errRep (GF := GF) x e ∗ (□ ∀ w, apierrors.apiErrAt x w -∗ ⌜b = match w with
      | .status st _ => decide (st.Reason' = go!"TooManyRequests") || decide (st.Code' = W32 429)
      | .plain => false⌝) ⊢ ⌜b = false⌝ := by
  rcases e with d | dl | _
  · iintro ⟨#H, #Hq⟩
    simp only [errRep]
    ihave #Hp := deepRO_plain wp_Unwrap x d hf $$ H
    ihave %Hr := Hq $$ Hp
    ipureintro; exact Hr
  · simp only [errRep, apierrors.tooLargeErrIs, apierrors.apiErrAt]
    iintro ⟨⟨⟨%st, %cs, ⟨%l, %h, #Hl, #Hds⟩, %hst, -⟩, %l', %st', %dv, ⟨%h', %hc, -⟩, #Hl', -⟩, #Hq⟩
    rw [h] at h'
    have hll : l = l' := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h'
      exact GoGlobalContext.intoVal_inj_loc h'
    subst hll
    icombine Hl Hl' gives %Hst
    simp only [k8s_io.apimachinery.pkg.api.errors.StatusError.mk.injEq] at Hst
    subst Hst
    ihave %Hr := Hq $$ %(.status st cs) [Hds]
    · iexists l
      iframe Hl Hds
      ipureintro; exact h
    ipureintro
    rw [Hr]
    simp only [hst.1, hc]
    rfl
  · exact hf.elim

end views

end k8s_correctness
end EtcdGrove
end Perennial
