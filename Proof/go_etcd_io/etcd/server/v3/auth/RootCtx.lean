/-
The process-local root identity of etcd-io/etcd#22493 (`server/auth/store.go`, branch
`pr-verify/etcd-22493`): `WithRootInternal(ctx, store)` stores, at the unexported key
`internalRootContextKey{}`, an `internalRootContextValue{store, revision}`, and the store's
`AuthInfoFromCtx` returns root at that revision for a context that carries one of its own store
(checked before the request's token).

* `rootKeyVal`: the key `internalRootContextKey{}`, as an `any`.
* `rootValIs v o`: what `ctx.Value(rootKeyVal)` may return for the context's root value `o`:
  `some x`, the value `x` (an `internalRootContextValue`); `none`, anything not of that type
  (`nil`, or a value of another type).
* `ctxRootIs ctx o` (persistent): the context `ctx` carries `o`: its `Value(rootKeyVal)`, from
  any goroutine, returns `rootValIs v o` (the shape of `traceutil.ctxTraceIs`).
* `rootInfoIf st o a err`: what `st.AuthInfoFromCtx` returns for a context that carries `o`: if
  `o` is a value of the store `st` itself (`x.store' = st`), no error and `nil` (auth disabled)
  or a fresh info for `root` at `x.revision'`.

Every context carries some `o` (`context.ValueInternalRoot.spec`, at the trust boundary: Go's
contract of `Context.Value`, "successive calls to Value with the same key return the same
result"). The key's type is unexported, so only package `auth` can store a value at it, and only
`WithRootInternal` does (the Go code; not a fact of the proof, which takes any context).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The key `internalRootContextKey{}`, as an `any`. -/
abbrev rootKeyVal : GoInterface :=
  interface.mkOk internalRootContextKey.ty #(zero_val internalRootContextKey)

/-- A root value `x`, as an `any`. -/
abbrev rootValAny (x : internalRootContextValue) : GoInterface :=
  interface.mkOk internalRootContextValue.ty #x

/-- What a context's `Value(internalRootContextKey{})` may return, for its root value `o`. -/
def rootValIs (v : GoInterface) : Option internalRootContextValue → Prop
  | some x => v = rootValAny x
  | none => v = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, v = GoInterface.ok ii ∧
      ii.ty ≠ internalRootContextValue.ty

/-- **The context `ctx` carries the root value `o`** (persistent): its
`Value(internalRootContextKey{})`, from any goroutine, returns it (`rootValIs`). -/
def ctxRootIs (ctx : GoInterfaceOk) (o : Option internalRootContextValue) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF,
    ▷ (∀ v : GoInterface, ⌜rootValIs v o⌝ -∗ Φ #v) -∗
      WP (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #rootKeyVal)) {{ Φ }})

instance ctxRootIs_persistent (ctx : GoInterfaceOk) (o : Option internalRootContextValue) :
    Persistent (ctxRootIs (GF := GF) ctx o) := by
  unfold ctxRootIs; infer_instance

/-- **What `st.AuthInfoFromCtx` returns for a context carrying `o`**: for a root value of `st`
itself, no error, and `nil` (auth disabled) or an info for `root` at the value's revision;
nothing more for another store's value or none. -/
def rootInfoIf (st : Loc) (o : Option internalRootContextValue) (a : Loc) (err : GoInterface) :
    IProp GF :=
  match o with
  | some x => iprop(⌜x.store' ≠ st⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ (⌜a = null⌝ ∨
      (⌜a ≠ null⌝ ∗ aiF go!"Username" a ↦□ go!"root" ∗ aiF go!"Revision" a ↦□ x.revision'))))
  | none => iprop(True)

instance rootInfoIf_persistent (st : Loc) (o : Option internalRootContextValue) (a : Loc)
    (err : GoInterface) : Persistent (rootInfoIf (GF := GF) st o a err) := by
  unfold rootInfoIf; cases o <;> infer_instance

/-- **`c` carries `parent`'s root value** (persistent): what a context derived from `parent` with
a value at another key does (`valueCtx.Value` asks the parent for a key not equal to its own). -/
def ctxRootKept (parent c : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ o : Option internalRootContextValue, ctxRootIs parent o -∗ ctxRootIs c o)

instance ctxRootKept_persistent (parent c : GoInterfaceOk) :
    Persistent (ctxRootKept (GF := GF) parent c) := by
  unfold ctxRootKept; infer_instance

theorem ctxRootKept_refl (c : GoInterfaceOk) : ⊢ ctxRootKept (GF := GF) c c := by
  iunfold ctxRootKept
  imodintro
  iintro %o Hc
  iexact Hc

/-- The store's token provider is the built-in JWT one (`as.tokenProvider.(*tokenJWT)`). -/
def jwtProvider (st : Loc) : IProp GF :=
  iprop(∃ (tp : TokenProvider) (ti : GoInterfaceOk), aF go!"tokenProvider" st ↦□ tp ∗
    ⌜tp = GoInterface.ok ti ∧ ti.ty = go.GoType.PointerType tokenJWT.ty⌝)

instance jwtProvider_persistent (st : Loc) : Persistent (jwtProvider (GF := GF) st) := by
  unfold jwtProvider; infer_instance

end defs

section ctxdefs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`c` is a context derived from `parent`** (persistent): described as `parent` is, with
other values (what a `valueCtx` over `parent` is: `WithValue`, grpc's `NewIncomingContext`). -/
def ctxDerived (parent c : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ cd : context.ContextDesc (IProp GF), context.isContext parent cd -∗
    ∃ vs : GMap GoInterface GoInterface, context.isContext c { cd with Values := vs })

instance ctxDerived_persistent (parent c : GoInterfaceOk) :
    Persistent (ctxDerived (GF := GF) parent c) := by
  unfold ctxDerived; infer_instance

/-- A context is derived from itself. -/
theorem ctxDerived_refl (c : GoInterfaceOk) : ⊢ ctxDerived (GF := GF) c c := by
  iunfold ctxDerived
  imodintro
  iintro %cd Hc
  iexists cd.Values
  iexact Hc

end ctxdefs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Nothing to show for a context that carries no root value of `st`. -/
theorem rootInfoIf_other (st : Loc) (o : Option internalRootContextValue) (a : Loc)
    (err : GoInterface) (h : ∀ x, o = some x → x.store' ≠ st) :
    ⊢ rootInfoIf (GF := GF) st o a err := by
  cases o with
  | none => unfold rootInfoIf; iintro; ipureintro; trivial
  | some x =>
    unfold rootInfoIf
    ileft; ipureintro; exact h x rfl

/-- No info and no error (auth disabled) meets `rootInfoIf`. -/
theorem rootInfoIf_nil (st : Loc) (o : Option internalRootContextValue) :
    ⊢ rootInfoIf (GF := GF) st o null GoInterface.nil := by
  cases o with
  | none => unfold rootInfoIf; iintro; ipureintro; trivial
  | some x =>
    unfold rootInfoIf
    iright; isplitr
    · ipureintro; rfl
    ileft; ipureintro; rfl

end lemmas

end auth
end EtcdGrove
end Perennial
