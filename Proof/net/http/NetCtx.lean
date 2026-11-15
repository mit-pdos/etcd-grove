/-
**What net/http reads of a request's context** (k8s 7f-4, Addendum T-h0, decided by etcd-grove-81,
2026-11-13; `notes/renewhttp-value-refuted.md`). Lean-first.

A `*http.Transport`'s round trip reads the request context's `Value` at keys of the standard
library's own unexported types, which `context.isContext` (and etcd's `srvCtxWeak`) say nothing of:
`httptrace.ContextClientTrace(ctx)` reads `clientEventContextKey{}` (go1.27.3
`net/http/transport.go:614, 1870`; a `*ClientTrace` there makes the transport call its hooks), and
the dial and lookup paths read `nettrace.TraceKey{}` (a `*nettrace.Trace`, whose hooks are called:
`net/dial.go:535, 778`, `net/lookup.go:313`) and `nettrace.LookupIPAltResolverKey{}` (a function
that replaces the resolver: `net/lookup.go:321`). A context whose `Value` panics at the first key
refuted `leasehttp.RenewHTTP.spec` (`TestRenewHTTPValuePanics`, `examples/premisefix/streamctx`).

* `http.netCtxOk ctx` (persistent): `ctx.Value` returns `nil` at the three keys (`context.valueAt`,
  the WP form `LibKeys.lean` defines): what `RenewHTTP`'s premise takes.
* `http.netCtxOkC ctx` (persistent): the same in Perennial's chain form (`ctxValue`), which
  `WithCancel` and the deadline constructors carry (`ctxValueFrom`, `http.netCtxOkC_from`) and which
  grpc's model gives of a stream's run context (`srvRawStreamIs`); back to the WP form by
  `http.netCtxOk_of_netCtxOkC`; from the WP form at a context of a type `context.value()` does not
  special-case (etcd's `cancellableContext`) by `http.netCtxOkC_raw`.

The keys' types are translated types-only (`net/http/httptrace`, `internal/nettrace`, `etc/goose.py`
project `etcd`).
-/
module

public import Perennial.Proof.context
public import Proof.context.LibKeys
public import GeneratedProof.net.http.httptrace
public import GeneratedProof.internal.nettrace

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

/-- `httptrace`'s `clientEventContextKey{}` as `ctx.Value` takes it (the empty struct, as `any`). -/
abbrev httptrace.clientEventKeyAny : GoInterface :=
  interface.mkOk _root_.Perennial.net.http.httptrace.clientEventContextKey.ty
    #(zero_val _root_.Perennial.net.http.httptrace.clientEventContextKey)

/-- `nettrace.TraceKey{}` as `ctx.Value` takes it. -/
abbrev nettrace.traceKeyAny : GoInterface :=
  interface.mkOk _root_.Perennial.internal.nettrace.TraceKey.ty
    #(zero_val _root_.Perennial.internal.nettrace.TraceKey)

/-- `nettrace.LookupIPAltResolverKey{}` as `ctx.Value` takes it. -/
abbrev nettrace.lookupIPAltResolverKeyAny : GoInterface :=
  interface.mkOk _root_.Perennial.internal.nettrace.LookupIPAltResolverKey.ty
    #(zero_val _root_.Perennial.internal.nettrace.LookupIPAltResolverKey)

/-- The three keys net/http's client reads. -/
abbrev http.netKeys : List GoInterface :=
  [httptrace.clientEventKeyAny, nettrace.traceKeyAny, nettrace.lookupIPAltResolverKeyAny]

/-- **`ctx` holds nothing at net/http's keys** (persistent): `ctx.Value(k)` returns `nil`, from any
goroutine, at `httptrace`'s `clientEventContextKey{}`, `nettrace.TraceKey{}` and
`nettrace.LookupIPAltResolverKey{}`: no client trace hooks, no network trace hooks, no alternative
resolver, and no panic. -/
def http.netCtxOk (ctx : GoInterfaceOk) : IProp GF :=
  iprop(context.valueAt ctx httptrace.clientEventKeyAny (· = GoInterface.nil) ∗
    context.valueAt ctx nettrace.traceKeyAny (· = GoInterface.nil) ∗
    context.valueAt ctx nettrace.lookupIPAltResolverKeyAny (· = GoInterface.nil))

instance http.netCtxOk_persistent (ctx : GoInterfaceOk) :
    Persistent (http.netCtxOk (GF := GF) ctx) := by
  unfold http.netCtxOk; infer_instance

variable [package_sem : _root_.Perennial.context.Assumptions]

/-- **`ctx` holds nothing at net/http's keys, as Perennial's chain says** (persistent): `http.netCtxOk`
with `context.value`'s chain (`ctxValue`) in place of the WP form, so that `WithCancel` and the
deadline constructors carry it (`ctxValueFrom`). -/
def http.netCtxOkC (ctx : GoInterfaceOk) : IProp GF :=
  iprop(_root_.Perennial.context.ctxValue ctx httptrace.clientEventKeyAny (· = GoInterface.nil) ∗
    _root_.Perennial.context.ctxValue ctx nettrace.traceKeyAny (· = GoInterface.nil) ∗
    _root_.Perennial.context.ctxValue ctx nettrace.lookupIPAltResolverKeyAny (· = GoInterface.nil))

instance http.netCtxOkC_persistent (ctx : GoInterfaceOk) :
    Persistent (http.netCtxOkC (GF := GF) ctx) := by
  unfold http.netCtxOkC; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- None of net/http's keys is a `*int` (Perennial's side condition of `ctxValueFrom`). -/
theorem http.netKeys_notIntPtr (k : GoInterface) (hk : k ∈ http.netKeys) :
    _root_.Perennial.context.notIntPtrKey k := by
  intro ki h
  simp only [http.netKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;>
    simp only [GoInterface.ok.injEq] at h <;> subst h
  · unfold _root_.Perennial.net.http.httptrace.clientEventContextKey.ty; simp
  · unfold _root_.Perennial.internal.nettrace.TraceKey.ty; simp
  · unfold _root_.Perennial.internal.nettrace.LookupIPAltResolverKey.ty; simp

/-- **The chain form gives the WP form**, what `RenewHTTP` takes. -/
theorem http.netCtxOk_of_netCtxOkC (ctx : GoInterfaceOk) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ http.netCtxOkC ctx ⊢ http.netCtxOk ctx := by
  iintro ⟨#Hpkg, #H⟩
  unfold http.netCtxOkC
  icases H with ⟨#H1, #H2, #H3⟩
  unfold http.netCtxOk
  isplitl []
  · iapply context.valueAt_of_ctxValue; iframe #
  isplitl []
  · iapply context.valueAt_of_ctxValue; iframe #
  · iapply context.valueAt_of_ctxValue; iframe #

/-- **`WithCancel` and the deadline constructors carry the chain form** (`ctxValueFrom`). -/
theorem http.netCtxOkC_from (parent child : GoInterfaceOk) :
    _root_.Perennial.context.ctxValueFrom (GF := GF) parent child ∗ http.netCtxOkC parent ⊢
      http.netCtxOkC child := by
  iintro ⟨#Hf, #H⟩
  unfold http.netCtxOkC
  icases H with ⟨#H1, #H2, #H3⟩
  unfold _root_.Perennial.context.ctxValueFrom
  isplitl []
  · iapply Hf
    · ipureintro; exact http.netKeys_notIntPtr _ (by simp)
    iexact H1
  isplitl []
  · iapply Hf
    · ipureintro; exact http.netKeys_notIntPtr _ (by simp)
    iexact H2
  · iapply Hf
    · ipureintro; exact http.netKeys_notIntPtr _ (by simp)
    iexact H3

/-- **A context of a type `context.value()` does not special-case** (etcd's `cancellableContext`):
its own `Value` is what the chain calls, so the WP form gives the chain form. -/
theorem http.netCtxOkC_raw (ctx : GoInterfaceOk)
    (hty : ctx.ty ∉ _root_.Perennial.context.valueSpecialTypes) :
    http.netCtxOk (GF := GF) ctx ⊢ http.netCtxOkC ctx := by
  iintro #H
  unfold http.netCtxOk
  icases H with ⟨#H1, #H2, #H3⟩
  unfold http.netCtxOkC
  unfold context.valueAt
  isplitl []
  · iapply _root_.Perennial.context.ctxValue_other ctx _ _ hty; iexact H1
  isplitl []
  · iapply _root_.Perennial.context.ctxValue_other ctx _ _ hty; iexact H2
  · iapply _root_.Perennial.context.ctxValue_other ctx _ _ hty; iexact H3

end laws

end EtcdGrove
end Perennial
