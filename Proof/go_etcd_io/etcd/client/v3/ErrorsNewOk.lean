/-
**`errors.New`'s errors are client errors grpc's `status` accepts** (2026-10-18; until then the
watcher's premise `errorsNewOk`), and **so are every context's `Err()`s** (`ctxErrClientAllW_of`;
until then the premise `ctxErrClientAllW`). Lean-first (no Rocq counterpart).

`ctxErrClientAllW_of`: from Go's contract of `Context.Err` (`context.ErrAny`, the trust boundary:
`nil`, or the value of `context.Canceled` or `context.DeadlineExceeded`) and those two errors'
facts: leaf errors without `Is` whose `Error()` returns (`ContextReadErrs`, the read package's
premise), of types other than `rpctypes.EtcdError` and without `GRPCStatus` (`ContextErrsClient`:
Go's `*errorString` and `deadlineExceededError`, whose methods are `Error`, `Timeout`,
`Temporary`).

`errorsNewOk_of`: from Perennial's `errors.New` (a fresh `*errorString` whose `Error()` returns the
message, `mvcc.wp_New_errorString`) and the method-set facts of `*errorString`, which the
semantics leaves uninterpreted (premises, as Perennial's `context.ErrorStringIsError`): it is a
leaf without `Is` (`ErrorStringLeaf`) and has no `GRPCStatus` method
(`ErrorStringNoGRPCStatus`: Go's `errors` package defines only `Error`); and `rpctypes.EtcdError`
implements `error` (`hAs`, the client's KV premise).
-/
module

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
class ErrorStringNoGRPCStatus [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] : Prop where
  noGRPCStatus : methodSet (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) !!
      go!"GRPCStatus" ≠
    some (go.Signature [] false
      [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty])

section ctxClass
open Iris Iris.BI
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- **`context.Canceled`'s and `context.DeadlineExceeded`'s types** (a premise, as
`ContextReadErrs`: Go's `*errorString` and `deadlineExceededError`, neither `rpctypes.EtcdError`,
neither with a `GRPCStatus` method; method sets are uninterpreted in the semantics). -/
class ContextErrsClient : Prop where
  errs : isPkgInit (PROP := IProp GF) pkg_id.context ⊢
    ctxErrTyOk _root_.Perennial.context.Canceled ∗ ctxErrTyOk _root_.Perennial.context.DeadlineExceeded

end ctxClass

namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]
variable [rp_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

/-- **`errorsNewOk` holds** (see the file header). -/
theorem errorsNewOk_of [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
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
    refine ⟨ErrorStringLeaf.leaf _, ?_⟩
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
  · unfold errorStringSpec
    iintro !> %Ψ HΨ
    iapply Herr
    inext
    iapply HΨ
  isplitr
  · ipureintro; exact ErrorStringLeaf.leaf _
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
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    EtcdGrove.errMsgOk (GF := GF) e ⊢ ⌜clientErr (GoInterface.ok e)⌝ ∗ statusErrOk (GoInterface.ok e) := by
  iintro #Hm
  isplitl
  · ipureintro
    refine ⟨hAs, fun ii h => ?_⟩
    cases h
    refine ⟨hl, ?_⟩
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
  · unfold errorStringSpec
    iintro !> %Ψ HΨ
    iunfold EtcdGrove.errMsgOk at Hm
    iapply Hm $$ [] [HΨ]
    · itrivial
    inext
    iintro %msg -
    iapply HΨ
  isplitr
  · ipureintro; exact hl
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
theorem eofOk_of_init [_root_.Perennial.io.Assumptions] [ErrorStringLeaf] [ErrorStringNoGRPCStatus]
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ eofOk := by
  iintro #Hpkg
  ihave #Hv := _root_.Perennial.io.eof_of_init $$ Hpkg
  iunfold _root_.Perennial.errors.newVar at Hv
  icases Hv with ⟨%x, #Hpt, #Hmsg⟩
  ihave #Hm : EtcdGrove.errMsgOk (GF := GF)
      ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩ $$ []
  · iunfold EtcdGrove.errMsgOk
    iapply (errorMsg_triple (GF := GF)) $$ Hmsg
  have hl := errorString_leaf x
  have hty : go.GoType.PointerType _root_.Perennial.errors.errorString.ty ≠
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty := by
    unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
  ihave ⟨%Hc, #Hs⟩ := clientErr_statusErrOk_of_leaf _ hl.2.1 hl.2.2
    ErrorStringNoGRPCStatus.noGRPCStatus hty hAs $$ Hm
  unfold eofOk
  iintro !> %err #He
  iunfold eofIs at He
  icombine Hpt He gives %Heq
  subst Heq
  isplitr
  · ipureintro
    exact ⟨nofun, Hc⟩
  iexact Hs

/-- **Every context's `Err()` returns client errors** (see the file header). -/
theorem ctxErrClientAllW_of (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ ctxErrClientAllW := by
  iintro #Hp
  ihave ⟨#HC, #HD⟩ := EtcdGrove.ContextReadErrs.errs $$ Hp
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
  ihave ⟨%Hcc, #Hsc⟩ := clientErr_statusErrOk_of_leaf ec Hlc.2.1 Hlc.2.2 Htc.1 Htc.2 hAs $$ Hmc
  ihave ⟨%Hcd, #Hsd⟩ := clientErr_statusErrOk_of_leaf ed Hld.1 Hld.2.1 Htd.1 Htd.2 hAs $$ Hmd
  unfold ctxErrClientAllW
  iintro !> %ctx %cs #Hctx
  unfold ctxErrClient
  iintro !> %cl %Φ Hpre HΦ
  iapply (wp_ErrAny ctx cs cl) $$ [Hpre] [HΦ]
  · iframe #; iexact Hpre
  inext
  iintro %err ⟨Hpost, Hid⟩
  icases Hid with (%Hn | ⟨%Ht, (#Hv | #Hv)⟩)
  · subst Hn
    iapply HΦ $$ Hpost
    · ipureintro; exact ⟨hAs, fun ii h => by cases h⟩
    · iapply statusErrOk_nil
  · icombine Hv Hec gives %Heq
    subst Heq
    iapply HΦ $$ Hpost
    · ipureintro; exact Hcc
    · iexact Hsc
  · icombine Hv Hed gives %Heq
    subst Heq
    iapply HΦ $$ Hpost
    · ipureintro; exact Hcd
    · iexact Hsd

end proofs

end client
end EtcdGrove
end Perennial
