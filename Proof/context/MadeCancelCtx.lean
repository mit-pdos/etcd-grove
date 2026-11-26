/-
**A `*cancelCtx` made by `context`** (k8s 7f-4, Addendum T-j, 2026-11-13; T-h5's option (A),
decided by etcd-grove-81): an opaque, persistent fact of a location, `context.madeCancelCtx c`, that
the weak context vocabulary `v3rpc.ctxDoneErr` (`SrvCtxWeak.lean`) states of the `*cancelCtx` a
context's `Value(&cancelCtxKey)` and `parentCancelCtx` find, in place of Perennial's `isCancelCtx`,
whose invariant (`cancelCtxInv`: a stored error is `Canceled`'s or `DeadlineExceeded`'s value) is false
of a `*timerCtx` made over etcd's require-leader wrapper once it is done (Addendum T-h1). TRUSTED: the
opaque and its law `context.madeCancelCtx_of_isCancelCtx` are part of the trust base. Lean-first.
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `madeCancelCtx`'s fact, raw (opaque). -/
opaque context.madeCancelCtxRaw (c : Loc) : IProp GF

/-- **The `*cancelCtx` at `c` was made by `context`, or is a zero `cancelCtx` from `reflect.New`**
(persistent, opaque; TRUSTED; k8s 7f-4, Addendum T-j; widened 2026-11-26,
`notes/axiom-review/madecancelctx-per-index.md`). Either:
* `c` was allocated by one of `context`'s allocations of a `cancelCtx` (go1.27.3
  `src/context/context.go`): `withCancel`'s `&cancelCtx{}` (`:278`; `WithCancel` `:241`,
  `WithCancelCause` `:269`, and `WithDeadlineCause`'s `WithCancel(parent)` when the parent's deadline is
  earlier, `:637`), the `cancelCtx` embedded in `WithDeadlineCause`'s `&timerCtx{…}` (`:641`;
  `WithDeadline`, `WithTimeout(Cause)`), or the one embedded in `AfterFunc`'s `&afterFuncCtx{…}`
  (`:327`); and its fields (`mu`, `done`, `children`, `err`, `cause`, `Context`) are read and written
  only by `context`'s code, under its own `mu` where `context` takes it; or
* `c` is a fresh zero `cancelCtx` a program made with `reflect.New` of `cancelCtx`'s type (reached
  through `reflect.New.spec` and `reflNew_pointsto`), whose state is `context`'s protocol at the start:
  no `done` channel, no `err`, no `children`, no `cause`; it differs from one `context` made only in
  its embedded `Context` field, which is `nil`.

So, in Go, `context`'s functions may use it as a parent: `parentCancelCtx` (`:383-397`) compares its
`done`, `propagateCancel` (`:476-528`) registers a child in its `children` or cancels the child with
its `err` and `cause`, under its `mu`, `removeChild` (`:400-414`) deletes a child under its `mu`, and
`Cause` (`:289-307`) reads its `cause` under its `mu`, without a panic or a data race. None of them
reads the found `*cancelCtx`'s `Context` field (`propagateCancel` writes the *child's*, `:477, 514`);
only its own `cancel` (`removeChild(c.Context, c)`, `:578`), `Value` (`:446`), `String` (`:544`) and
the promoted `Deadline` do, and those panic on the `reflect.New` zero value (nil interface).

**The obligation of every consumer.** A spec or axiom that takes `madeCancelCtx` (directly, through
`madeCancelCtxAny`, or through `v3rpc.ctxDoneErr`/`v3rpc.ctxChildErr`'s `"#HValue"`/`"#HParentCC"`)
must never read, nor let Go read, the found `*cancelCtx`'s embedded `Context` field: it may reach
the found `*cancelCtx` only through `parentCancelCtx`, `propagateCancel`, `removeChild` and `Cause`.
The consumers (2026-11-26, `grep -rn 'madeCancelCtx\|ctxDoneErr\|ctxChildErr' --include=*.lean`; none
in Perennial):
* `leasehttp.RenewHTTP.wp_proof` (TRUSTED axiom; premise `v3rpc.ctxDoneErr ctx cd` of
  `leasehttp.RenewHTTP.spec`): its Go reaches the found `*cancelCtx` only inside `context`, through
  net/http's `WithCancelCause(req.Context())` (go1.27.3 `net/http/transport.go:675`) and
  `WithDeadline` (`client.go:373, 380`, a client timeout; `withCancel`/`WithDeadlineCause` →
  `propagateCancel`, `:476-528`: `parentCancelCtx` and `Cause` of the request context, then the found
  one's `mu`, `err`, `cause`, `children`), their cancel functions (the child's `cancel` →
  `removeChild(child.Context, …)`, `:578, 400-414`: the found one's `mu`, `children`) and `Cause`
  (`:289-307`: `mu`, `cause`; `transport.go:698, 1640, 1651`). Its other context calls (`Done`, `Err`,
  `Value` at other keys, `WithoutCancel`, `transport.go:1596`) are on the request context or on
  children `context` made over it, whose `value` walk (`:776-800`) goes from a child's `Context` to
  the request context and down its own chain; a `reflect.New` zero `*cancelCtx` is never on that
  chain (each context of it needs the `"#HDeadline"` WP of `ctxDoneErr`/`isContext`, which the zero
  value's promoted `Deadline`, a call through its nil `Context`, does not have).
* `v3rpc.wp_WithTimeout_weak` (TRUSTED axiom): a producer, not a consumer: its premise is
  `srvCtxWeak parent pd` (Perennial's `isCancelCtx`, not `madeCancelCtx`); its post gives
  `madeCancelCtx` (`v3rpc.ctxChildErr`) only of the `cancelCtx` embedded in the `*timerCtx` it
  allocates (`:641`) or of `withCancel`'s (`:278`): made by `context`.
* `EtcdServer.waitLeader.spec` (premise `v3rpc.ctxDoneErr ctx cd`; proved over the real code):
  its Go only selects on `ctx.Done()`; a verified program gets no points-to and no method spec of
  the found `*cancelCtx` from `madeCancelCtx` (no law eliminates it), so it cannot read its fields.
* The proofs that pass it on (`EtcdServer.LeaseRenew`, `EtcdServer.PromoteMember`, over the real
  code) and the laws that give it (`madeCancelCtx_of_isCancelCtx`, `madeCancelCtxAny_of_isCancelCtxAny`,
  `v3rpc.ctxDoneErr_of_srvCtxWeak`, `_of_isContext`, `_of_child`): verified, or producers; they read
  nothing of the found `*cancelCtx` for the same reason.
A new consumer is added to this list with its reason.

It says nothing of the errors `c` stores (unlike Perennial's `isCancelCtx`, whose invariant has
them be context errors): a `*timerCtx` made over a parent already done stores the parent's `Err()`,
which for etcd's require-leader wrapper is `rpctypes.ErrGRPCNoLeader` (Addendum T-h1,
`TestWithTimeoutWeak`).

What it excludes (Addendum T-h5): any other value of type `*cancelCtx`, which a program can build
with `reflect` (the type is unexported): a nil pointer (`parentCancelCtx` loads its `done` through it:
`TestRenewHTTPNilCancelCtxPanics`), or a non-nil copy of a real one (its own `mu` over the real one's
`children` map: a data race).

Given by: `context.madeCancelCtx_of_isCancelCtx` (every `isCancelCtxOfA` is one, of `context`'s
allocations or of a `reflect.New` zero value), and the local axiom `v3rpc.wp_WithTimeout_weak` (of
the new `*timerCtx`'s embedded `cancelCtx`, through `v3rpc.ctxChildErr`'s `"#HValue"` and
`"#HParentCC"`). No other spec may give it. -/
def context.madeCancelCtx (c : Loc) : IProp GF := iprop(□ context.madeCancelCtxRaw c)

instance context.madeCancelCtx_persistent (c : Loc) :
    Persistent (context.madeCancelCtx (GF := GF) c) := by
  unfold context.madeCancelCtx; infer_instance

/-- **The result of `Value(&cancelCtxKey)`**, as `context.isCancelCtxAny` with `madeCancelCtx` in
place of `isCancelCtx` (persistent): if it is a `*cancelCtx`, `context` made it; `nil`, or a value of
another dynamic type, otherwise. -/
def context.madeCancelCtxAny (v : GoInterface) : IProp GF :=
  match v with
  | interface.ok ii =>
    if ii.ty = go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty then
      iprop(∃ c : Loc, ⌜ii.v = #c⌝ ∗ context.madeCancelCtx c)
    else iprop(True)
  | interface.nil => iprop(True)

instance context.madeCancelCtxAny_persistent (v : GoInterface) :
    Persistent (context.madeCancelCtxAny (GF := GF) v) := by
  unfold context.madeCancelCtxAny
  split
  · split <;> infer_instance
  · infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- (TRUSTED; k8s 7f-4, Addendum T-j) **Every `*cancelCtx` Perennial's model describes was made by
`context`**: `isCancelCtx c` (`Perennial/Proof/context/Base.lean`) is a `sync.isMutex` of `c`'s `mu`
whose lock invariant owns `c`'s `children` and `cause` fields, and an invariant owning its `done` and
`err` cells; Perennial's proofs establish it of the locations `context`'s constructors allocate
(`wp_withCancel_`, the `timerCtx` of `wp_WithDeadlineCause`), the struct type `cancelCtx` is
unexported, and a verified program has the field points-tos of a `cancelCtx` by one route only:
`reflect.New.spec` with `reflNew_pointsto` (`Proof/reflect/Values.lean`), at `cancelCtx`'s type
(`reflect.ValueOf(ctx).Elem().Type()` of a real one), gives a fresh zero `cancelCtx` and its
points-to, from which a proof can build `isCancelCtxOfA` of that location (for any `A`: the zero
value's `err` is nil). That is harmless, and inside `madeCancelCtx`'s meaning (its second case): the
zero value differs from one `context` made only in its embedded `Context` field, which is `nil`, and
no consumer of `madeCancelCtx` reads that field (`madeCancelCtx`'s list; Go evidence:
`notes/axiom-review/madecancelctx-per-index.md`, a zero `*cancelCtx` behind a wrapper is a working
parent for `WithTimeout`, `WithCancel` and `Cause` under `-race`). No other location gets one:
a `reflect` copy of a real one shares its `children` map, which the real one's lock invariant owns
(`ownMap`), so both cannot hold; a nil pointer has no fields (`structFieldRef` of a non-plain struct
gives no cell); Go code outside `context` cannot name the type.
The argument is independent of the error index `A` (only `context`'s constructors, and `reflect.New`'s
zero value above, make a `cancelCtx`; the type is unexported; no other field points-tos are given out;
`madeCancelCtx` says nothing about errors): it is stated per index since perennial#705 (`isCancelCtxOf` became `∃ A`), with the same
meaning as the `isCancelCtx c` form (`isCancelCtx c` is `∃ γ P A, isCancelCtxOfA c γ P A`). -/
axiom context.madeCancelCtx_of_isCancelCtx (c : Loc) (γ : _root_.Perennial.context.ContextNames)
    (P : IProp GF) (A : GoInterface → Prop) :
    (_root_.Perennial.context.isCancelCtxOfA c γ P A : IProp GF) ⊢ context.madeCancelCtx c

/-- `isCancelCtxAny ⊢ madeCancelCtxAny`, by `madeCancelCtx_of_isCancelCtx`. -/
theorem context.madeCancelCtxAny_of_isCancelCtxAny (v : GoInterface) :
    (_root_.Perennial.context.isCancelCtxAny v : IProp GF) ⊢ context.madeCancelCtxAny v := by
  unfold _root_.Perennial.context.isCancelCtxAny context.madeCancelCtxAny
  rcases v with ii | _
  · simp only
    split
    · iintro ⟨%c, %Hv, #Hc⟩
      iexists c
      isplitr
      · ipureintro; exact Hv
      iunfold _root_.Perennial.context.isCancelCtx at Hc
      icases Hc with ⟨%γ, %P, #Hc⟩
      ihave ⟨%A, #HA⟩ := _root_.Perennial.context.isCancelCtxOf_A c γ P $$ Hc
      iapply context.madeCancelCtx_of_isCancelCtx c γ P A
      iexact HA
    · iintro -; itrivial
  · iintro -; itrivial

end laws

end EtcdGrove
end Perennial
