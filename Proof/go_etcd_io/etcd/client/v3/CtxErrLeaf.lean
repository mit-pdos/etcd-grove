/-
**A done context's error, as the retry interceptor's `contextErrToGRPCErr` takes it** (prove-ps2-wrb,
2026-11-22: `waitRetryBackoff` and `contextErrToGRPCErr` proved over the real code; until then
`waitRetryBackoff` was a trust-boundary axiom). Lean-first (no Rocq counterpart).

`ctxErrLeaf err`: a non-nil leaf error of a context error's shape whose `Error()` stably returns one
of Go's two context messages, a pointer if an `*errors.errorString`: what `errors.Is` needs of it
(against `context.DeadlineExceeded` and `context.Canceled`: a one-error tree without an `Is` method,
`errors.errorIsTree_leaf`) and what makes `status.Error(c, err.Error())` no handler's error. Both
contexts `ctxOk` admits with a Done channel give it once done: Perennial's model (`isCtxErr`:
`Canceled`'s `*errorString` or `DeadlineExceeded`'s `deadlineExceededError{}`,
`ctxErrLeaf_of_isCtxErr`) and `ctxErrs` (`ctxErrsErr`'s non-nil error, `ctxErrLeaf_of_errs`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk errorMsgIs ctxErrMsg ctxErrShape)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- A `*status.Error` leaf is a client error (given `EtcdError` is an `errors.As` target; moved
here from `WatchResponse__Err.lean`, a proof, 2026-11-22). -/
theorem clientErr_statusError (e : GoInterfaceOk) (hl : errors.isLeafError e)
    (hty : e.ty = go.GoType.PointerType google_golang_org.grpc.internal.status.Error.ty)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    clientErr (GoInterface.ok e) := by
  refine ⟨hAs, fun ii h => ?_⟩
  cases h
  refine ⟨hl, ?_, by simp [clientErrTys, hty]⟩
  unfold errors.AsTypeTyped
  have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
      go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
  rw [hu]
  simp only [go.isInterfaceType]
  intro h
  rw [hty] at h
  simp [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty] at h

/-- **A done context's error** (persistent): a non-nil leaf error (`errors.isLeafError`) of a
context error's shape (`ctxErrShape`: no `Is` method, no `EtcdError`), a pointer if an
`*errors.errorString` (`errPtrOk`), whose `Error()` stably returns one of Go's two context messages
(`ctxErrMsg`, `errorMsgIs`). -/
def ctxErrLeaf (err : GoInterface) : IProp GF :=
  iprop(∃ (e : GoInterfaceOk) (m : GoString),
    ⌜err = GoInterface.ok e ∧ ctxErrMsg m ∧ ctxErrShape e ∧ errors.isLeafError e ∧
      errPtrOk err⌝ ∗ errorMsgIs e m)

instance ctxErrLeaf_persistent (err : GoInterface) : Persistent (ctxErrLeaf (GF := GF) err) := by
  unfold ctxErrLeaf; infer_instance

/-- **Perennial's context errors** (`isCtxErr`: `Canceled`'s `errors.New("context canceled")`, a
`*errorString` whose `s` field holds the message for good, or `DeadlineExceeded`'s
`deadlineExceededError{}`, whose `Error()` is the literal `"context deadline exceeded"`). -/
theorem ctxErrLeaf_of_isCtxErr (err : GoInterface) :
    context.isCtxErr (GF := GF) err ⊢ ctxErrLeaf err := by
  iintro #He
  iunfold context.isCtxErr at He
  unfold ctxErrLeaf
  icases He with (⟨-, %x, %hx, #Hs⟩ | ⟨-, %hv⟩)
  · subst hx
    have hl := errorString_leaf x
    iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩, go!"context canceled"
    isplitl []
    · ipureintro
      refine ⟨rfl, Or.inl rfl, ⟨?_, hl.2.2⟩, hl.2.1, errPtrOk_ptr x⟩
      unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty; nofun
    · unfold errorMsgIs
      iintro !> %Φ HΦ
      rw [method_unfold]
      wp_auto
      iexact HΦ
  · subst hv
    have h := fun m => go.method_set_is (t := _root_.Perennial.context.deadlineExceededError.ty) m
    have hAs := h go!"As"; have hU := h go!"Unwrap"; have hIs := h go!"Is"
    simp only [go.methodSetLookup_cons, go.methodSetLookup_nil, gooseReduceIteDecide] at hAs hU hIs
    iexists ⟨_root_.Perennial.context.deadlineExceededError.ty,
      #(zero_val _root_.Perennial.context.deadlineExceededError)⟩, go!"context deadline exceeded"
    isplitl []
    · ipureintro
      refine ⟨rfl, Or.inr rfl, ⟨?_, by simp [hIs]⟩,
        by simp [_root_.Perennial.errors.isLeafError, hAs, hU], ?_⟩
      · unfold go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
          _root_.Perennial.context.deadlineExceededError.ty
        simp
      · apply errPtrOk_of_ty
        unfold _root_.Perennial.context.deadlineExceededError.ty; simp
    · unfold errorMsgIs
      iintro !> %Φ HΦ
      wp_method_call
      unfold _root_.Perennial.context.deadlineExceededError.Error.impl
      wp_auto
      iexact HΦ

/-- **A `ctxErrs` context's error once done** (`ctxErrsErr`'s `.Done` case: non-nil, accepted by
grpc's `status`, no caller's `errors.New` value, and of a context error's shape and message). -/
theorem ctxErrLeaf_of_errs (err : GoInterface) (hne : err ≠ GoInterface.nil) :
    statusErrOk (GF := GF) err ∗ errCellOk err ∗
      (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString),
        ⌜err = GoInterface.ok e ∧ ctxErrMsg m ∧ ctxErrShape e⌝ ∗ errorMsgIs e m) ⊢
      ctxErrLeaf err := by
  iintro ⟨#Hs, #Hc, Hm⟩
  icases Hm with (%Hn | ⟨%e, %m, %Hem, #Hm⟩)
  · exact absurd Hn hne
  obtain ⟨rfl, hm, hsh⟩ := Hem
  iunfold statusErrOk at Hs
  ihave ⟨-, %Hl, -, -⟩ := Hs $$ %e %rfl
  ihave %Hp := errPtrOk_of_cell (GoInterface.ok e) $$ Hc
  unfold ctxErrLeaf
  iexists e, m
  iframe Hm
  ipureintro
  exact ⟨rfl, hm, hsh, Hl, Hp⟩

end defs

end EtcdGrove
end Perennial
