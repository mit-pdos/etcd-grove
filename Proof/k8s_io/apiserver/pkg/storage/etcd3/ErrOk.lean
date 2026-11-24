/-
Lean-first (no Rocq counterpart).

# The producers' errors are ones the watcher's error paths accept (`kErrOk`; k8s 7f-5a-P step 5)

Each error `startWatching` and `syncPaginated` hand to `sendError` (`notes/k8s-7f5a-draft.md` §11):

- `kErrOk_intro`: the shape of every proof below: the pure facts of a leaf error outside the
  corrupt-object error's type (`errors.AsLeafTy`, trusted text approved by etcd-grove-81
  2026-11-15), its `Error()`, and its `Code()`, `GRPCStatus()` and `Status()` where its type has them;
- `kErrOk_errorString`: an `*errors.errorString` whose `Error()` returns (`fmt.ErrorfPlain`'s, E3:
  `parseEvent`'s, `syncPaginated`'s and `GetCurrentResourceVersion`'s own; a context's `Canceled`);
- `kErrOk_client`: an error of etcd's client (`kClientErr`: its four types, `clientErrTys`), a
  `*status.Error`'s status code through E1 (`status.statusAt`, `status.Status.Code.spec`);
- `kErrOk_statusError`: a `*StatusError` with a `Failure` status (`interpretListError`'s 410,
  `transformErrorToEvent`'s); `StatusError.Error` and `Status` are translated with their bodies.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Spec.errors.AsLeafTy
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Code
public import Spec.google_golang_org.grpc.status.Status__Code

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode

section errs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- The target of `interpretWatchError`'s `errors.As` is an error type (`*corruptObjectDeletedError`
has `Error() string`). -/
theorem corrupt_asTarget :
    _root_.Perennial.errors.AsTarget (go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) := by
  right
  go_type_set

/-- **The shape of `kErrOk`**: a leaf error (`isLeafError`) whose dynamic type is not
`*corruptObjectDeletedError` (`errors.AsLeafTy` gives `As` false), with no `Format` method, its
value of the comparands' shapes, its `Error()` returning, and its `Code()` (as an `etcdError`),
`GRPCStatus().Code()` (as a `grpcError`) and `Status()` (as an `APIStatus`) behaving. -/
theorem kErrOk_intro (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG)) (e : GoInterfaceOk)
    (hshape : (e.ty = go.GoType.PointerType _root_.Perennial.errors.errorString.ty → ∃ x : Loc, e.v = #x) ∧
      (e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
        ∃ y : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError, e.v = #y))
    (hF : methodSet e.ty !! go!"Format" = none ∧ methodSet e.ty !! go!"Error" = some noArgStringSig)
    (hleaf : _root_.Perennial.errors.isLeafError e)
    (hne : e.ty ≠ go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty)
    (hund : underlying e.ty ≠
      go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
    fmt.stringMethodSpec (GF := GF) e go!"Error" -∗
    □ (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.etcdError.ty = true⌝ -∗
      ∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
        WP (App (Val #(methods e.ty go!"Code" e.v)) (Val #())) {{ Φ }}) -∗
    □ (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.grpcError.ty = true⌝ -∗
      ∃ s : Loc,
        (∀ Φ : val → IProp GF, ▷ Φ #s -∗
          WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
        (∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
          WP (App (Val #(methods (go.GoType.PointerType google_golang_org.grpc.status.Status.ty)
            go!"Code" #s)) (Val #())) {{ Φ }})) -∗
    □ (⌜go.typeSetContains e.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = true⌝ -∗
      ∀ Φ : val → IProp GF,
        ▷ (∀ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, ⌜st.Status' = go!"Failure"⌝ -∗
          Φ #st) -∗
        WP (App (Val #(methods e.ty go!"Status" e.v)) (Val #())) {{ Φ }}) -∗
    kErrOk (GoInterface.ok e) := by
  iintro #Perr #Hs #Hc #Hg #Ha
  unfold kErrOk
  iexists e
  isplitr
  · ipureintro; rfl
  imodintro
  iframe Hs Hc Hg Ha
  isplitr
  · ipureintro; exact hshape
  isplitr
  · ipureintro; exact hF
  iintro %l %v %Φ Hl HΦ
  have hts : go.typeSetContains e.ty
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) =
        false := by
    simp only [go.typeSetContains, go.is_underlying]
    simpa using hne
  have hund' : go.isInterfaceType (underlying (go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty)) = false →
      underlying e.ty ≠ underlying (go.GoType.PointerType
        k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty) := by
    intro _
    rw [go.is_underlying (t := go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty)]
    exact hund
  wp_apply (wp_AsLeafTy e l v corrupt_asTarget hleaf hts hund') $$ [Hl]
  · iframe
  iintro Hl
  iapply HΦ $$ Hl

/-- **An `errors.New`/`fmt.ErrorfPlain` error is one the watcher's error paths accept.** -/
theorem kErrOk_errorString (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG)) (x : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
    fmt.stringMethodSpec (GF := GF) ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
      go!"Error" -∗
    kErrOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #Perr #Hs
  have hleaf : _root_.Perennial.errors.isLeafError
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ := by
    have h1 := go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"As"
    have h2 := go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Unwrap"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil] at h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> simp_all
  have hF : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !! go!"Format" =
      none := by
    have := go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Format"
    simpa [go.methodSetLookup_cons, go.methodSetLookup_nil] using this
  have hE : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !! go!"Error" =
      some noArgStringSig := by
    have := go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty) go!"Error"
    simpa [go.methodSetLookup_cons, go.methodSetLookup_nil, noArgStringSig] using this
  iapply (kErrOk_intro wp_AsLeafTy ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
    ⟨fun _ => ⟨x, rfl⟩, fun h => by
      exfalso; revert h; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp⟩
    ⟨hF, hE⟩ hleaf
    (by unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
          _root_.Perennial.errors.errorString.ty; simp)
    (by rw [go.is_underlying (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)]
        unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
          _root_.Perennial.errors.errorString.ty; simp)) $$ Perr Hs
  · iintro !> %h
    exfalso
    revert h
    go_type_set
    simp
  · iintro !> %h
    exfalso
    revert h
    go_type_set
    simp
  · iintro !> %h
    exfalso
    revert h
    go_type_set
    simp

/-- `kErrOk_intro`'s premises a dynamic type refutes: no `Code()`, `GRPCStatus()` or `Status()`. -/
theorem kErrOk_none_etcd (e : GoInterfaceOk)
    (h : go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.etcdError.ty = false) :
    ⊢ □ (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.etcdError.ty = true⌝ -∗
      ∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
        WP (App (Val #(methods e.ty go!"Code" e.v)) (Val #())) {{ Φ }}) := by
  iintro !> %h'
  rw [h] at h'; cases h'

theorem kErrOk_none_grpc (e : GoInterfaceOk)
    (h : go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.grpcError.ty = false) :
    ⊢ □ (⌜go.typeSetContains e.ty k8s_io.apiserver.pkg.storage.etcd3.grpcError.ty = true⌝ -∗
      ∃ s : Loc,
        (∀ Φ : val → IProp GF, ▷ Φ #s -∗
          WP (App (Val #(methods e.ty go!"GRPCStatus" e.v)) (Val #())) {{ Φ }}) ∗
        (∀ Φ : val → IProp GF, ▷ (∀ c : google_golang_org.grpc.codes.Code, Φ #c) -∗
          WP (App (Val #(methods (go.GoType.PointerType google_golang_org.grpc.status.Status.ty)
            go!"Code" #s)) (Val #())) {{ Φ }})) := by
  iintro !> %h'
  rw [h] at h'; cases h'

theorem kErrOk_none_api (e : GoInterfaceOk)
    (h : go.typeSetContains e.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false) :
    ⊢ □ (⌜go.typeSetContains e.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = true⌝ -∗
      ∀ Φ : val → IProp GF,
        ▷ (∀ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, ⌜st.Status' = go!"Failure"⌝ -∗
          Φ #st) -∗
        WP (App (Val #(methods e.ty go!"Status" e.v)) (Val #())) {{ Φ }}) := by
  iintro !> %h'
  rw [h] at h'; cases h'

/-- **An error of etcd's client is one the watcher's error paths accept** (one of `clientErrTys`, a
leaf grpc's `status` accepts, a pointer if an `*errors.errorString` (`errPtrOk`); a `*status.Error`'s
status is read-only, E1). -/
theorem kErrOk_clientP [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG))
    (wp_ECode : rpctypes.EtcdError.Code.spec (GF := GF) (hG := hG))
    (wp_SCode : status.Status.Code.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (Hc : err ≠ GoInterface.nil ∧ clientErr err) (Hptr : errPtrOk err) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢ go_etcd_io.etcd.cache.v3.statusErrOk err -∗
      kErrOk err := by
  iintro #Perr #Hs
  obtain ⟨hne0, hc⟩ := Hc
  cases err with
  | nil => exact absurd rfl hne0
  | ok e =>
  obtain ⟨-, hty, hT⟩ := hc.2 e rfl
  iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hs
  ihave ⟨⟨%m, #Hm⟩, %Hleaf, #Hg, %HF⟩ := Hs $$ %e %rfl
  ihave #Hstr : fmt.stringMethodSpec (GF := GF) e go!"Error" $$ []
  · unfold fmt.stringMethodSpec
    iintro !> %Φ HΦ
    iunfold go_etcd_io.etcd.cache.v3.errorMsgIs at Hm
    iapply Hm
    inext
    iapply HΦ
  obtain ⟨t, v⟩ := e
  simp only [clientErrTys, List.mem_cons, List.not_mem_nil, _root_.or_false] at hT
  rcases hT with ht | ht | ht | ht <;> subst ht
  · -- a `*status.Error`: its status's code (E1)
    iapply (kErrOk_intro wp_AsLeafTy _ ⟨fun h => by
        exfalso; revert h; unfold google_golang_org.grpc.internal.status.Error.ty
          _root_.Perennial.errors.errorString.ty; simp,
      fun h => by exfalso; revert h; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp⟩
      HF Hleaf
      (by unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
            google_golang_org.grpc.internal.status.Error.ty; simp)
      (by rw [go.is_underlying (t := go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty)]
          unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
            google_golang_org.grpc.internal.status.Error.ty; simp)) $$ Perr Hstr
    · iapply kErrOk_none_etcd
      go_type_set <;> simp
    · iintro !> %-
      iunfold go_etcd_io.etcd.cache.v3.grpcErrMethodsOk at Hg
      icases Hg with ⟨Hgs, -⟩
      have hm : methodSet (go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty) !!
          go!"GRPCStatus" = some (go.Signature [] false
            [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]) := by
        have := go.MethodSetIs.method_set_is
          (t := go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty) go!"GRPCStatus"
        simpa [go.methodSetLookup_cons, go.methodSetLookup_nil] using this
      ihave ⟨%s, %sc, %sm, #Hw, #Hro⟩ := Hgs $$ %hm
      iexists s
      isplitr
      · iintro %Φ HΦ
        iapply Hw $$ HΦ
      · iintro %Φ HΦ
        wp_apply (wp_SCode s sc sm) $$ [Hro]
        · iexact Hro
        iapply HΦ
    · iapply kErrOk_none_api
      go_type_set <;> simp
  · -- an `rpctypes.EtcdError`: its `Code()`
    have hni : go.isInterfaceType (underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) =
        false := by
      have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
          go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
      rw [hu]
      simp only [go.isInterfaceType]
    unfold errors.AsTypeTyped at hty
    rw [hni] at hty
    obtain ⟨y, hy⟩ := hty rfl
    simp only at hy
    subst hy
    iapply (kErrOk_intro wp_AsLeafTy _ ⟨fun h => by
        exfalso; revert h; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp,
      fun _ => ⟨y, rfl⟩⟩
      HF Hleaf
      (by unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp)
      (by rw [go.is_underlying (t := go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)]
          unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying; simp)) $$ Perr Hstr
    · iintro !> %- %Φ HΦ
      wp_apply (wp_ECode y)
      iapply HΦ
    · iapply kErrOk_none_grpc
      go_type_set <;> simp
    · iapply kErrOk_none_api
      go_type_set <;> simp
  · -- an `*errors.errorString` (`io.EOF`, `context.Canceled`): a pointer (`errCellOk`)
    obtain ⟨x, hx⟩ := Hptr _ rfl rfl
    simp only at hx
    subst hx
    iapply (kErrOk_intro wp_AsLeafTy _ ⟨fun _ => ⟨x, rfl⟩, fun h => by
        exfalso; revert h; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp⟩
      HF Hleaf
      (by unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
            _root_.Perennial.errors.errorString.ty; simp)
      (by rw [go.is_underlying (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)]
          unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
            _root_.Perennial.errors.errorString.ty; simp)) $$ Perr Hstr
    · iapply kErrOk_none_etcd
      go_type_set <;> simp
    · iapply kErrOk_none_grpc
      go_type_set <;> simp
    · iapply kErrOk_none_api
      go_type_set <;> simp
  · -- `context.DeadlineExceeded`
    iapply (kErrOk_intro wp_AsLeafTy _ ⟨fun h => by
        exfalso; revert h; unfold _root_.Perennial.context.deadlineExceededError.ty
          _root_.Perennial.errors.errorString.ty; simp,
      fun h => by
        exfalso; revert h
        unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
          _root_.Perennial.context.deadlineExceededError.ty
        simp⟩
      HF Hleaf
      (by unfold _root_.Perennial.context.deadlineExceededError.ty; simp)
      (by rw [go.is_underlying (t := _root_.Perennial.context.deadlineExceededError.ty)]
          unfold _root_.Perennial.context.deadlineExceededError.underlying; simp)) $$ Perr Hstr
    · iapply kErrOk_none_etcd
      go_type_set <;> simp
    · iapply kErrOk_none_grpc
      go_type_set <;> simp
    · iapply kErrOk_none_api
      go_type_set <;> simp

/-- **An error of etcd's client is one the watcher's error paths accept** (`kClientErr`; its cell
gives the pointer, `errPtrOk_of_cell`). -/
theorem kErrOk_client [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG))
    (wp_ECode : rpctypes.EtcdError.Code.spec (GF := GF) (hG := hG))
    (wp_SCode : status.Status.Code.spec (GF := GF) (hG := hG)) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢ kClientErr err -∗ kErrOk err := by
  iintro #Perr #H
  iunfold kClientErr at H
  icases H with ⟨%Hc, #Hs, #Hcl⟩
  ihave %Hp := errPtrOk_of_cell err $$ Hcl
  iapply (kErrOk_clientP wp_AsLeafTy wp_ECode wp_SCode err Hc Hp) $$ Perr Hs

/-- **A `*StatusError` with a `Failure` status is one the watcher's error paths accept**
(`StatusError.Error` returns its message, `Status` its status: both translated). -/
theorem kErrOk_statusError (wp_AsLeafTy : errors.AsLeafTy.spec (GF := GF) (hG := hG)) (l : Loc)
    (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status) (hst : st.Status' = go!"Failure") :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢
    l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st -∗
    kErrOk (interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)
      #l) := by
  iintro #Perr #Hl
  have hms := fun m => go.MethodSetIs.method_set_is
    (t := go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) m
  have hleaf : _root_.Perennial.errors.isLeafError
      ⟨go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty, #l⟩ := by
    have h1 := hms go!"As"
    have h2 := hms go!"Unwrap"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil] at h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> simp_all
  have hF : methodSet (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) !!
      go!"Format" = none := by
    simpa [go.methodSetLookup_cons, go.methodSetLookup_nil] using hms go!"Format"
  have hE : methodSet (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) !!
      go!"Error" = some noArgStringSig := by
    simpa [go.methodSetLookup_cons, go.methodSetLookup_nil, noArgStringSig] using hms go!"Error"
  ihave #Hstr : fmt.stringMethodSpec (GF := GF)
      ⟨go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty, #l⟩ go!"Error" $$ []
  · unfold fmt.stringMethodSpec
    iintro !> %Φ HΦ
    simp only []
    rw [k8s_io.apimachinery.pkg.api.errors.StatusError.TypeAssumptions.ptr_unfold'Error.method_unfold]
    ihave Hl' := Hl
    iStructNamed Hl'
    iStructNamed ErrStatus
    wp_auto
    iapply HΦ
  iapply (kErrOk_intro wp_AsLeafTy _ ⟨fun h => by
      exfalso; revert h; unfold k8s_io.apimachinery.pkg.api.errors.StatusError.ty
        _root_.Perennial.errors.errorString.ty; simp,
    fun h => by exfalso; revert h; unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; simp⟩
    ⟨hF, hE⟩ hleaf
    (by unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
          k8s_io.apimachinery.pkg.api.errors.StatusError.ty; simp)
    (by rw [go.is_underlying (t := go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)]
        unfold k8s_io.apiserver.pkg.storage.etcd3.corruptObjectDeletedError.ty
          k8s_io.apimachinery.pkg.api.errors.StatusError.ty; simp)) $$ Perr Hstr
  · iapply kErrOk_none_etcd
    go_type_set <;> simp
  · iapply kErrOk_none_grpc
    go_type_set <;> simp
  · iintro !> %- %Φ HΦ
    simp only []
    rw [k8s_io.apimachinery.pkg.api.errors.StatusError.TypeAssumptions.ptr_unfold'Status.method_unfold]
    ihave Hl' := Hl
    iStructNamed Hl'
    wp_auto
    iapply HΦ
    ipureintro; exact hst

end errs

end k8s
end EtcdGrove
end Perennial
