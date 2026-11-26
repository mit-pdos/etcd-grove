/-
**`errors.New`'s errors are client errors grpc's `status` accepts** (2026-10-18; until then the
watcher's premise `errorsNewOk`), and **so are every context's `Err()`s** (`ctxErrClientAllW_of`;
until then the premise `ctxErrClientAllW`). Lean-first (no Rocq counterpart).

`ctxErrClientAllW_of`: from Go's contract of `Context.Err` (`context.ErrAny`, the trust boundary:
`nil`, or the value of `context.Canceled` or `context.DeadlineExceeded`) and those two errors'
facts: leaf errors without `Is` whose `Error()` returns (`ContextReadErrs.errs_strong`, the read
package's), of types other than `rpctypes.EtcdError` and without `GRPCStatus`
(`ContextErrsClient.errs`: Go's `*errorString` and `deadlineExceededError`, whose methods are
`Error`, `Timeout`, `Temporary`); both from Perennial's `context.isInit` (premises until
ctx-leaf-fix, 2026-11-25).

`errorsNewOk_of`: from Perennial's `errors.New` (a fresh `*errorString` whose `Error()` returns the
message, `mvcc.wp_New_errorString`) and the method-set facts of `*errorString` (theorems of the
method sets goose emits, `errorStringLeaf_inst`, `errorStringNoGRPCStatus_inst`): it is a
leaf without `Is` (`ErrorStringLeaf`) and has no `GRPCStatus` method
(`ErrorStringNoGRPCStatus`: Go's `errors` package defines only `Error`); and `rpctypes.EtcdError`
implements `error` (`hAs`, the client's KV premise).
-/
module

public import Perennial.Golang.Theory.TypeSet
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf
public import Proof.errors.NewVar
public import Perennial.Proof.io.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.read.Init
public import Spec.context.ErrAny

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- The method set of `*errors.errorString` has no `GRPCStatus` method (Go's `errors` package
gives it only `Error`; grpc's `status.FromError` would call it). -/
class ErrorStringNoGRPCStatus [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  noGRPCStatus : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !!
      go!"GRPCStatus" ≠
    some (go.Signature [] false
      [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])

/-- `ErrorStringNoGRPCStatus` holds: `*errorString`'s method set (goose's `ptr_method_set`) is
`Error` only. -/
instance errorStringNoGRPCStatus_inst [GooseExts] [GoGlobalContext] [GoLocalContext]
    [GoSemanticsFunctions] [_root_.Perennial.errors.Assumptions] : ErrorStringNoGRPCStatus := by
  have h := go.method_set_is (t := go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
    go!"GRPCStatus"
  simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
  exact ⟨by simp [h]⟩

section ctxClass
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The error variable `g` holds an error of a type other than `rpctypes.EtcdError`, without a
`GRPCStatus` method. -/
def ctxErrTyOk (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
    ⌜methodSet e.ty !! go!"GRPCStatus" ≠
        some (go.Signature [] false
          [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]) ∧
      e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝)

/-- **`context.Canceled`'s and `context.DeadlineExceeded`'s types** (a premise, the class
`ContextErrsClient`, until ctx-leaf-fix, 2026-11-25): Go's `*errorString` and
`deadlineExceededError`, neither `rpctypes.EtcdError`, neither with a `GRPCStatus` method; from
Perennial's `context.isInit` (`"#HCanceledCell"`, `"#HDeadlineExceededTy"`) and the method sets
goose emits. -/
theorem ContextErrsClient.errs [_root_.Perennial.context.Assumptions]
    [_root_.Perennial.errors.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢
      ctxErrTyOk _root_.Perennial.context.Canceled ∗
        ctxErrTyOk _root_.Perennial.context.DeadlineExceeded := by
  iintro #Hp
  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Hp
  iNamed Hci
  icases HCanceledCell with ⟨%x, #Hx, -⟩
  isplitl
  · iunfold ctxErrTyOk
    iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
    iframe Hx
    ipureintro
    refine ⟨ErrorStringNoGRPCStatus.noGRPCStatus, ?_⟩
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
  · iunfold ctxErrTyOk
    iexists ⟨_root_.Perennial.context.deadlineExceededError.ty,
      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩
    iframe HDeadlineExceededTy
    ipureintro
    have h := go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) go!"GRPCStatus"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at h
    refine ⟨by simp [h], ?_⟩
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
      _root_.Perennial.context.deadlineExceededError.ty
    intro h; cases h

end ctxClass

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [rp_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- **`errorsNewOk` holds** (see the file header). -/
theorem errorsNewOk_of
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ⊢ errorsNewOk (GF := GF) := by
  unfold errorsNewOk
  iintro !> %msg %Φ HΦ
  iapply (mvcc.wp_New_errorString (GF := GF) msg) $$ [] [HΦ]
  · itrivial
  inext
  iintro %x #Herr
  iapply HΦ
  · ipureintro
    refine ⟨by simp, hAs, fun ii h => ?_⟩
    cases h
    refine ⟨ErrorStringLeaf.leaf _, ?_, by simp [clientErrTys]⟩
    unfold errors.AsTypeTyped
    have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
        go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
    rw [hu]
    simp only [go.isInterfaceType]
    intro h
    simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty] at h
  unfold closeErrOk
  isplitl
  rotate_left
  · ipureintro
    refine ⟨fun _ => ⟨hAs, fun ii h => ?_⟩, errPtrOk_ptr x⟩
    cases h
    refine ⟨ErrorStringLeaf.leaf _, ?_, by simp [clientErrTys]⟩
    unfold errors.AsTypeTyped
    have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
        go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
    rw [hu]
    simp only [go.isInterfaceType]
    intro h
    simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty] at h
  unfold statusErrOk
  iintro !> %e %he
  cases he
  isplitr
  · iexists msg
    unfold errorMsgIs
    iexact Herr
  isplitr
  · ipureintro; exact ErrorStringLeaf.leaf _
  isplitr
  rotate_left
  · ipureintro; exact ⟨⟨ErrorStringLeaf.noFormat, EtcdGrove.errorString_errorSig⟩,
      stTypedErr_ptr _ (errorString_leaf x).1⟩
  unfold grpcErrMethodsOk
  isplitl
  · iintro %h
    exact absurd h ErrorStringNoGRPCStatus.noGRPCStatus
  · iintro %h
    exact absurd h ErrorStringLeaf.noIs

/-- **A leaf error of a type other than `rpctypes.EtcdError`, without `Is` or `GRPCStatus`,
whose `Error()` returns, is a client error grpc's `status` accepts.** -/
theorem clientErr_statusErrOk_of_leaf (e : GoInterfaceOk) (hl : errors.isLeafError e)
    (hIs : methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]))
    (hG : methodSet e.ty !! go!"GRPCStatus" ≠ some (go.Signature [] false
      [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]))
    (hty : e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (hT : e.ty ∈ clientErrTys)
    (hF : methodSet e.ty !! go!"Format" = none)
    (hE : methodSet e.ty !! go!"Error" = some EtcdGrove.noArgStringSig)
    (hst : stTypedErr e) :
    EtcdGrove.errMsgOk (GF := GF) e ⊢ ⌜clientErr (GoInterface.ok e)⌝ ∗ statusErrOk (GoInterface.ok e) := by
  iintro #Hm
  isplitl
  · ipureintro
    refine ⟨hAs, fun ii h => ?_⟩
    cases h
    refine ⟨hl, ?_, hT⟩
    unfold errors.AsTypeTyped
    have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
        go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
    rw [hu]
    simp only [go.isInterfaceType]
    intro h; exact absurd h hty
  unfold statusErrOk
  iintro !> %e' %he
  cases he
  isplitr
  · iapply EtcdGrove.errMsgOk_msgIs $$ Hm
  isplitr
  · ipureintro; exact hl
  isplitr
  rotate_left
  · ipureintro; exact ⟨⟨hF, hE⟩, hst⟩
  unfold grpcErrMethodsOk
  isplitl
  · iintro %h
    exact absurd h hG
  · iintro %h
    exact absurd h hIs

/-- **`io.EOF` is a client error grpc's `status` accepts** (`eofOk`), from `io`'s package fact:
`io.isInit` keeps `EOF`'s value, an `errors.New("EOF")` error (`io.eof_of_init`), a leaf
`*errorString` without `Is` or `GRPCStatus` (`ErrorStringLeaf`, `ErrorStringNoGRPCStatus`) whose
`Error()` returns. -/
theorem eofOk_of_init [_root_.Perennial.io.Assumptions]
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ eofOk := by
  iintro #Hpkg
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hpkg
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, #_, #Hmsg⟩
  ihave #Hm : EtcdGrove.errMsgOk (GF := GF)
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ $$ []
  · iunfold EtcdGrove.errMsgOk
    iapply (errorMsg_triple (GF := GF)) $$ Hmsg
  have hl := errorString_leaf x
  have hty : go.GoType.PointerType _root_.Perennial.errors.errorString.ty ≠
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
  ihave ⟨%Hc, #Hs⟩ := clientErr_statusErrOk_of_leaf _ hl.2.1 hl.2.2
    ErrorStringNoGRPCStatus.noGRPCStatus hty hAs (by simp [clientErrTys]) ErrorStringLeaf.noFormat
    EtcdGrove.errorString_errorSig (stTypedErr_ptr _ hl.1) $$ Hm
  unfold eofOk
  iintro !> %err #He
  iunfold eofIs at He
  icombine Hpt He gives %Heq
  subst Heq
  isplitr
  · ipureintro
    exact ⟨nofun, Hc⟩
  iexact Hs

/-- **`io.EOF` is a pointer** (`errPtrOk`; k8s 7f-5): its value is `errors.New("EOF")`'s
(`io.eof_of_init`). -/
theorem eofPtr_of_init [_root_.Perennial.io.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ □ ∀ err : GoInterface, eofIs err -∗ ⌜errPtrOk err⌝ := by
  iintro #Hpkg
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hpkg
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, -⟩
  iintro !> %err #He
  iunfold eofIs at He
  icombine Hpt He gives %Heq
  subst Heq
  ipureintro
  exact errPtrOk_ptr x

/-- **An `*errors.errorString`'s `Error()` returns its cell's message** (incomingof Part B): per run,
from the persistent `s` field. -/
theorem errorMsgIs_errorString (x : Loc) (m : GoString) :
    x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ m ⊢
      errorMsgIs (GF := GF)
        (interface.mk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) m := by
  iintro #Hs
  unfold errorMsgIs
  iintro !> %Φ HΦ
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- **`DeadlineExceeded`'s `Error()` returns `"context deadline exceeded"`** (incomingof Part B): its
method body is the literal (`context.go`). -/
theorem errorMsgIs_deadline [_root_.Perennial.context.Assumptions] :
    ⊢ errorMsgIs (GF := GF)
        (interface.mk _root_.Perennial.context.deadlineExceededError.ty
          #(zero_val _root_.Perennial.context.deadlineExceededError)) go!"context deadline exceeded" := by
  unfold errorMsgIs
  iintro !> %Φ HΦ
  wp_method_call
  unfold _root_.Perennial.context.deadlineExceededError.Error.impl
  wp_auto
  iexact HΦ

/-- **Every context's `Err()` returns client errors** (see the file header). -/
theorem ctxErrClientAllW_of [_root_.Perennial.context.Assumptions]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ ctxErrClientAllW := by
  iintro #Hp
  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs_strong $$ Hp
  ihave ⟨#HC2, #HD2⟩ := ContextErrsClient.errs $$ Hp
  iunfold EtcdGrove.errVarLeaf at HC
  icases HC with ⟨%ec, #Hec, %Hlc, #Hmc⟩
  icases HD with ⟨%ed, #Hed, %Hld, #Hmd⟩
  iunfold ctxErrTyOk at HC2
  icases HC2 with ⟨%ec', #Hec', %Htc⟩
  iunfold ctxErrTyOk at HD2
  icases HD2 with ⟨%ed', #Hed', %Htd⟩
  icombine Hec Hec' gives %Heqc
  icombine Hed Hed' gives %Heqd
  cases Heqc; cases Heqd
  -- (k8s 7e-1) their dynamic types, from `context`'s package fact
  ihave #Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Hp
  iNamed Hci
  icases HCanceledCell with ⟨%xc, #Hxc, -⟩
  icombine Hec Hxc gives %HtyC
  icombine Hed HDeadlineExceededTy gives %HtyD
  have hTc : ec.ty ∈ clientErrTys := by
    cases ec; simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at HtyC
    simp [clientErrTys, HtyC.1]
  have hTd : ed.ty ∈ clientErrTys := by
    cases ed; simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at HtyD
    simp [clientErrTys, HtyD.1]
  -- (#45) their values' typing: `Canceled`'s is a pointer, `DeadlineExceeded`'s `{}`
  have hstd : stTypedErr ed := by
    cases ed; simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at HtyD
    obtain ⟨h1, h2⟩ := HtyD; subst h1 h2; exact stTypedErr_deadline
  ihave ⟨%Hcc, #Hsc⟩ := clientErr_statusErrOk_of_leaf ec Hlc.2.1 Hlc.2.2.1 Htc.1 Htc.2 hAs hTc Hlc.2.2.2.2.1 Hlc.2.2.2.2.2
    (stTypedErr_ptr _ Hlc.1) $$ Hmc
  ihave ⟨%Hcd, #Hsd⟩ := clientErr_statusErrOk_of_leaf ed Hld.1 Hld.2.1 Htd.1 Htd.2 hAs hTd Hld.2.2.2.2.2.1 Hld.2.2.2.2.2.2
    hstd $$ Hmd
  unfold ctxErrClientAllW
  iintro !> %ctx %cs #Hctx
  unfold ctxErrClient
  iintro !> %cl %Φ Hpre HΦ
  iapply (wp_ErrAny ctx cs cl) $$ [Hpre] [HΦ]
  · iframe #; iexact Hpre
  inext
  iintro %err ⟨Hpost, Hid⟩
  icases Hid with (%Hn | ⟨%Ht, (⟨#Hv, %x, %Hx, #Hcell⟩ | ⟨#Hv, %Hnd⟩)⟩)
  · subst Hn
    iapply HΦ $$ Hpost
    · ipureintro; exact ⟨hAs, fun ii h => by cases h⟩
    · iapply statusErrOk_nil
    · iapply go_etcd_io.etcd.cache.v3.errCellOk_nil
    · ileft; ipureintro; rfl
  · icombine Hv Hec gives %Heq
    subst Heq
    iapply HΦ $$ Hpost
    · ipureintro; exact Hcc
    · iexact Hsc
    · -- (D37) `Canceled`'s cell holds `"context canceled"`
      rw [Hx]
      iapply go_etcd_io.etcd.cache.v3.errCellOk_of_cell x _
        (by simp [go_etcd_io.etcd.cache.v3.clientErrMsgs]) $$ Hcell
    · -- (incomingof Part B) `Error()` returns `"context canceled"`, of a context error's shape
      iright; iexists ec, go!"context canceled"
      have hx : ec = interface.mk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x :=
        GoInterface.ok.inj Hx
      isplitl []
      · ipureintro
        refine ⟨rfl, Or.inl rfl, ⟨Htc.2, Hlc.2.2.1⟩, fun h => ?_⟩
        rw [hx] at h
        exact absurd h (_root_.Perennial.context.deadlineExceededError_ne_ptr _).symm
      · rw [hx]; iapply errorMsgIs_errorString $$ Hcell
  · icombine Hv Hed gives %Heq
    subst Heq
    iapply HΦ $$ Hpost
    · ipureintro; exact Hcd
    · iexact Hsd
    · -- (D37) `DeadlineExceeded` is of no `*errorString` type
      iapply go_etcd_io.etcd.cache.v3.errCellOk_of_ty ed (Hnd ed rfl)
    · -- (incomingof Part B) `Error()` returns `"context deadline exceeded"`
      iright; iexists ed, go!"context deadline exceeded"
      have hd : ed = interface.mk _root_.Perennial.context.deadlineExceededError.ty
          #(zero_val _root_.Perennial.context.deadlineExceededError) := GoInterface.ok.inj HtyD
      isplitl []
      · ipureintro
        exact ⟨rfl, Or.inr rfl, ⟨Htd.2, Hld.2.1⟩, fun _ => by rw [hd]⟩
      · rw [hd]; iapply errorMsgIs_deadline

end proofs

end client
end EtcdGrove
end Perennial
