/-
`WithRequireLeader`'s result is a context the watch takes (k8s 7f-3a, T5-a): the axiom's
`Done()`/`Err()`/`Value(&cancelCtxKey)` transfers and `outgoingCtxOkC c` give
`watchCtx ctx s -∗ watchCtx c s` (`Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`; the axiom
states the parts, not `watchCtx`, for the axiom-tok gate); and, with its `Deadline()` and
`parentCancelCtx` transfers and `c`'s type (k8s 7f-5a, T5-e), `isContext ctx cd -∗ isContext c cd`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithRequireLeader

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **The parts make a `watchCtx`**: a context whose `Done()`, `Err()` and `Value(&cancelCtxKey)`
calls do what the parent's do, with grpc's outgoing metadata, is a context the watch takes at the
parent's descriptor. -/
theorem WithRequireLeader.watchCtx_of_post (ctx c : GoInterfaceOk)
    (s : _root_.Perennial.context.ContextDesc (IProp GF)) :
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #())) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #())) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Value" ctx.v))
          (Val #_root_.Perennial.context.cancelCtxKeyAny)) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Value" c.v))
          (Val #_root_.Perennial.context.cancelCtxKeyAny)) {{ Φ }}) ∗
    metadata.outgoingCtxOkC c ⊢
    context.watchCtx ctx s -∗ context.watchCtx c s := by
  iintro ⟨#HD, #HE, #HV, #HO⟩ #W
  unfold context.watchCtx
  iNamed W
  isplitr
  · imodintro
    iintro %Φ _ HΦ
    iapply HD
    iapply HDone $$ [] HΦ
    itrivial
  isplitr
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    iapply HE
    iapply HErr $$ Hpre HΦ
  isplitr
  · iexact HO
  · imodintro
    iintro %Φ _ HΦ
    iapply HV
    iapply HCC $$ [] HΦ
    itrivial

/-- **The parts make an `isContext`** (k8s 7f-5a, T5-e): a context whose `Deadline()`, `Done()`,
`Err()`, `Value(&cancelCtxKey)` and `parentCancelCtx` calls do what the parent's do, and whose type
is not `stopCtx`, is a context of Perennial's model at the parent's descriptor. -/
theorem WithRequireLeader.isContext_of_post (ctx c : GoInterfaceOk)
    (cd : _root_.Perennial.context.ContextDesc (IProp GF)) :
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #())) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #())) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Value" ctx.v))
          (Val #_root_.Perennial.context.cancelCtxKeyAny)) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Value" c.v))
          (Val #_root_.Perennial.context.cancelCtxKeyAny)) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val #(methods ctx.ty go!"Deadline" ctx.v)) (Val #())) {{ Φ }} -∗
        WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF,
        WP (App (Val (@! _root_.Perennial.context.parentCancelCtx))
          (Val #(GoInterface.ok ctx))) {{ Φ }} -∗
        WP (App (Val (@! _root_.Perennial.context.parentCancelCtx))
          (Val #(GoInterface.ok c))) {{ Φ }}) ∗
    ⌜c.ty ≠ _root_.Perennial.context.stopCtx.ty⌝ ⊢
    _root_.Perennial.context.isContext ctx cd -∗ _root_.Perennial.context.isContext c cd := by
  iintro ⟨#HD, #HE, #HV, #HDl, #HP, %Hty⟩ #W
  unfold _root_.Perennial.context.isContext _root_.Perennial.context.isContextDef
  iNamed W
  isplitr
  · imodintro
    iintro %Φ _ HΦ
    iapply HDl
    iapply HDeadline $$ [] HΦ
    itrivial
  isplitr
  · imodintro
    iintro %Φ _ HΦ
    iapply HD
    iapply HDone $$ [] HΦ
    itrivial
  isplitr
  · iintro %cl
    imodintro
    iintro %Φ Hpre HΦ
    iapply HE
    iapply HErr $$ Hpre HΦ
  isplitr
  · imodintro
    iintro %Φ _ HΦ
    iapply HV
    iapply HValue $$ [] HΦ
    itrivial
  isplitr
  · imodintro
    iintro %Φ Hcl HΦ
    iapply HE
    iapply HErrDone $$ Hcl HΦ
  isplitr
  · iexact HDoneFresh
  isplitr
  · icases HParentCC with ⟨%_, #HPC⟩
    isplitr
    · ipureintro; exact Hty
    · imodintro
      iintro %ch %cch %Φ Hdg Hcc %Hne HΦ
      iapply HP
      iapply HPC $$ Hdg Hcc %Hne HΦ
  · iexact HClosedchan

end laws

end EtcdGrove
end Perennial
