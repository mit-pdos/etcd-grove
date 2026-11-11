/-
**grpc's outgoing metadata, in the chain form** (premise-fixes-8, part C1, 2026-11-11; the Scope's
C.1, decision D3). Lean-first.

premise-fixes-7's `metadata.outgoingCtxOk ctx` (`LibKeys.lean`) is a WP fact about `ctx.Value`.
It does not cross `context.WithCancel`: Go's `value()` walks a `*cancelCtx`'s parent chain without
calling the parent's `Value`, so a WP fact of the parent says nothing of the child. Perennial's
`ctxValue` (`Perennial/Proof/context/CtxValue.lean`) is the chain form, which `WithCancel` and the
deadline constructors carry (`ctxValueFrom`). Client-side contexts pass through those constructors
before grpc reads them (`NewSession`, `Election.Observe`, the lessor, the watcher, the leasing
`KV`), so the facts the client's contracts carry are in that form:

* `metadata.outgoingCtxOkC ctx` (persistent): `ctx`'s outgoing metadata is one value `v` that
  `FromOutgoingContext` accepts (`outgoingRes`), as Perennial's chain says.

Laws (all proved): `Background()`, `TODO()` (`_background`, `_todo`); a child by `WithCancel`/the
deadline constructors (`_from`); a `valueCtx` at another key (`_valueCtx`) or at grpc's own key
holding a `rawMD` grpc made (`_ownKey`); a context of a type `value()` does not special-case, from
the WP form (`_raw`: k8s's `channelContext`, etcd's `valCtx`); and back to the WP form
(`outgoingCtxOk_of_C`), which the readers take (D3).
-/
module

public import Proof.context.LibKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **`ctx`'s outgoing metadata is grpc's, as Perennial's chain says** (persistent): one value `v`,
which `FromOutgoingContext` accepts, is what both `ctx.Value(mdOutgoingKey{})` and
`context.value(ctx, mdOutgoingKey{})` return. Carried by `WithCancel` and the deadline constructors
(`ctxValueFrom`) and by a `valueCtx` at another key. -/
def metadata.outgoingCtxOkC (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ v : GoInterface, ⌜metadata.outgoingRes v⌝ ∗
    _root_.Perennial.context.ctxValue ctx metadata.mdOutgoingKeyAny (· = v))

instance metadata.outgoingCtxOkC_persistent (ctx : GoInterfaceOk) :
    Persistent (metadata.outgoingCtxOkC (GF := GF) ctx) := by
  unfold metadata.outgoingCtxOkC; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

theorem metadata.outgoingRes_nil : metadata.outgoingRes GoInterface.nil := by
  left; intro vi h; cases h

theorem metadata.mdOutgoingKey_notIntPtr :
    _root_.Perennial.context.notIntPtrKey metadata.mdOutgoingKeyAny :=
  context.libKeys_notIntPtr _ (by simp)

theorem metadata.outgoingCtxOkC_background :
    ⊢ metadata.outgoingCtxOkC (GF := GF) _root_.Perennial.context.backgroundCtxVal := by
  unfold metadata.outgoingCtxOkC
  iexists GoInterface.nil
  isplitl []
  · ipureintro; exact metadata.outgoingRes_nil
  iapply _root_.Perennial.context.ctxValue_background

theorem metadata.outgoingCtxOkC_todo :
    ⊢ metadata.outgoingCtxOkC (GF := GF) _root_.Perennial.context.todoCtxVal := by
  unfold metadata.outgoingCtxOkC
  iexists GoInterface.nil
  isplitl []
  · ipureintro; exact metadata.outgoingRes_nil
  iapply _root_.Perennial.context.ctxValue_todo

/-- **A child by `WithCancel` or a deadline constructor** answers grpc's key as its parent. -/
theorem metadata.outgoingCtxOkC_from (parent child : GoInterfaceOk) :
    _root_.Perennial.context.ctxValueFrom (GF := GF) parent child ∗
      metadata.outgoingCtxOkC parent ⊢ metadata.outgoingCtxOkC child := by
  iintro ⟨#Hf, #Hp⟩
  unfold metadata.outgoingCtxOkC
  icases Hp with ⟨%v, %hv, #Hv⟩
  iexists v
  iframe %hv
  unfold _root_.Perennial.context.ctxValueFrom
  iapply Hf
  · ipureintro; exact metadata.mdOutgoingKey_notIntPtr
  iexact Hv

/-- Comparing a key with one of another dynamic type (or with `nil`) does not compare values. -/
theorem context.keyEqOk_of_ty_ne (k key : GoInterface)
    (hk : ∀ ki kk : GoInterfaceOk, k = GoInterface.ok ki → key = GoInterface.ok kk → ki.ty ≠ kk.ty) :
    ⊢ _root_.Perennial.context.keyEqOk (GF := GF) k key := by
  unfold _root_.Perennial.context.keyEqOk
  iintro !> %ki %kk %Φ %h
  obtain ⟨h1 | h1, h2⟩ := h
  · exact absurd h2 (hk ki kk h1.1 h1.2)
  · exact absurd h2.symm (hk kk ki h1.1 h1.2)

/-- **A `valueCtx` at a key of another type than grpc's** answers grpc's key as its parent. -/
theorem metadata.outgoingCtxOkC_valueCtx (q : Loc) (p : GoInterfaceOk) (key val : GoInterface)
    (hkey : ∀ kk : GoInterfaceOk, key = GoInterface.ok kk →
      kk.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty) :
    _root_.Perennial.context.vctxField q ↦□ (interface.ok p : GoInterface) ∗
      structFieldRef _root_.Perennial.context.valueCtx go!"key" q ↦□ key ∗
      structFieldRef _root_.Perennial.context.valueCtx go!"val" q ↦□ val ∗
      metadata.outgoingCtxOkC (GF := GF) p ⊢
      metadata.outgoingCtxOkC
        (interface.mk (go.GoType.PointerType _root_.Perennial.context.valueCtx.ty) #q) := by
  iintro ⟨#Hf, #Hk, #Hv, #Hp⟩
  have hne : metadata.mdOutgoingKeyAny ≠ key := by
    intro h
    exact hkey _ h.symm rfl
  unfold metadata.outgoingCtxOkC
  icases Hp with ⟨%v, %hv, #Hpv⟩
  iexists v
  iframe %hv
  iapply _root_.Perennial.context.ctxValue_valueCtx q p key val
  iframe #
  isplitl []
  · iapply context.keyEqOk_of_ty_ne
    intro ki kk h1 h2
    simp only [GoInterface.ok.injEq] at h1
    subst h1
    exact (hkey kk h2).symm
  · simp only [hne, ↓reduceIte]
    iexact Hpv

/-- **A `valueCtx` at grpc's own key** (`metadata.NewOutgoingContext`, `AppendToOutgoingContext`)
holding a `rawMD` grpc made answers it, whatever its parent. -/
theorem metadata.outgoingCtxOkC_ownKey [md_sem : google_golang_org.grpc.metadata.Assumptions]
    (q : Loc) (p : GoInterfaceOk) (val : GoInterface) (hval : metadata.builtRawMD val) :
    _root_.Perennial.context.vctxField q ↦□ (interface.ok p : GoInterface) ∗
      structFieldRef _root_.Perennial.context.valueCtx go!"key" q ↦□ metadata.mdOutgoingKeyAny ∗
      structFieldRef _root_.Perennial.context.valueCtx go!"val" q ↦□ val ⊢
      metadata.outgoingCtxOkC (GF := GF)
        (interface.mk (go.GoType.PointerType _root_.Perennial.context.valueCtx.ty) #q) := by
  iintro ⟨#Hf, #Hk, #Hv⟩
  unfold metadata.outgoingCtxOkC
  iexists val
  isplitl []
  · ipureintro; right; exact hval
  iapply _root_.Perennial.context.ctxValue_valueCtx q p metadata.mdOutgoingKeyAny val
  iframe #
  isplitl []
  · unfold _root_.Perennial.context.keyEqOk
    iintro !> %ki %kk %Φ %h HΦ
    obtain ⟨h1 | h1, -⟩ := h <;> obtain ⟨h1, h2⟩ := h1 <;>
      simp only [GoInterface.ok.injEq] at h1 h2 <;> subst h1 <;> subst h2 <;>
      simp only [decide_true] <;> wp_auto <;> iexact HΦ
  · simp only [↓reduceIte]
    ipureintro; trivial

/-- **A context of a type `value()` does not special-case** (k8s's `channelContext`, etcd's
`valCtx`): its own `Value` is what the chain calls, so the WP form gives the chain form. -/
theorem metadata.outgoingCtxOkC_raw (ctx : GoInterfaceOk)
    (hty : ctx.ty ∉ _root_.Perennial.context.valueSpecialTypes) :
    metadata.outgoingCtxOk (GF := GF) ctx ⊢ metadata.outgoingCtxOkC ctx := by
  iintro #H
  unfold metadata.outgoingCtxOk metadata.outgoingCtxOkC
  icases H with ⟨%v, %hv, #Hv⟩
  iexists v
  iframe %hv
  iapply _root_.Perennial.context.ctxValue_other ctx _ _ hty
  unfold context.valueAt
  iexact Hv

/-- **Back to the WP form**, what the readers take (`FromOutgoingContext`, `kaCtxOk`,
`AppendToOutgoingContext`'s premise; D3). -/
theorem metadata.outgoingCtxOk_of_C (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ metadata.outgoingCtxOkC ctx ⊢
      metadata.outgoingCtxOk ctx := by
  iintro ⟨#Hpkg, #H⟩
  unfold metadata.outgoingCtxOkC metadata.outgoingCtxOk
  icases H with ⟨%v, %hv, #Hv⟩
  iexists v
  iframe %hv
  iapply context.valueAt_of_ctxValue
  iframe #

/-- A child of `TODO()` (`WithCancel`, the deadline constructors) has grpc's outgoing metadata (none),
in the chain form. -/
theorem metadata.outgoingCtxOkC_todoFrom (ctx : GoInterfaceOk) :
    _root_.Perennial.context.ctxValueFrom (GF := GF) _root_.Perennial.context.todoCtxVal ctx ⊢
      metadata.outgoingCtxOkC ctx := by
  iintro #Hf
  iapply metadata.outgoingCtxOkC_from
  iframe #
  iapply metadata.outgoingCtxOkC_todo

/-- A child of `Background()`, in the chain form. -/
theorem metadata.outgoingCtxOkC_bgFrom (ctx : GoInterfaceOk) :
    _root_.Perennial.context.ctxValueFrom (GF := GF) _root_.Perennial.context.backgroundCtxVal ctx ⊢
      metadata.outgoingCtxOkC ctx := by
  iintro #Hf
  iapply metadata.outgoingCtxOkC_from
  iframe #
  iapply metadata.outgoingCtxOkC_background

end laws

end EtcdGrove
end Perennial
