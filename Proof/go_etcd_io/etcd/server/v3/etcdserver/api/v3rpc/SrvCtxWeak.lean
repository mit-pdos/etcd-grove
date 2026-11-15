/-
**A stream handler's weak context** (k8s 7f-4, T-f; `notes/k8s-7f4-draft.md` §2,
`notes/k8s-7f4-freeze.md` §2). Lean-first.

etcd's `newStreamInterceptor`, when the client requires a leader, hands the handler a
`*serverStreamWithCtx` whose `Context()` is a `*cancellableContext`: its `Err()` returns
`rpctypes.ErrGRPCNoLeader` once etcd's leader monitor cancels it, which is not a context error, so
the context is not an `isContext`. `srvCtxWeak c s` is what the handlers, and the trust-boundary
specs they pass the context to (`Tracer.Start`, `waitLeader`, `RenewHTTP`), take of it: `isContext`
with its two `Err` clauses weakened (`Err()` returns nil or some error at any time; once `Done` is
closed, a non-nil error that is a context error or etcd's no-leader error, `noLeaderErr`), its other
clauses (`Deadline`, `Done`, `Value(&cancelCtxKey)`, the parent-cancel facts) as `isContext`'s, which
the wrapper's promoted methods answer as its embedded `WithCancel` child does.
-/
module

public import Perennial.Proof.context
public import GeneratedProof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import Proof.go_etcd_io.etcd.server.v3.auth.CtxDone
public import Proof.context.MadeCancelCtx

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

/-- **The thread-token level a weak context's `Err()` is paid with** (k8s 7f-4, Freeze addendum
"T-f': Err pays a level token"; decided by etcd-grove-81, 2026-11-12): level 4. etcd's wrapper's
`Err` takes `c.lock.RLock()`, whose reader slot (Perennial's `ownRWMutex`, `2^30 - 1` per lock, the
bound of Go's reader counter) comes from a thread pool at this level (`init_RWMutex_threadPoolL`):
the caller lends `levelTok 4` for the call and gets it back. Level 4 is reserved for it: grpc's run
splits a thread token into levels 0-3 (`threadTok_levels0123`, `InvGrpcRun.lean`: 0 the handler's
own, used by the lessor's and leases' pools, `lessorLvl = leaseLvl = 0`; 1 `raftPoolN`; 2 the
revoke pools; 3 `srvRunN`) and `threadTokFrom 4`, and no pool of the repository is at a level
above 3. -/
abbrev v3rpc.ctxErrLvl : Nat := 4

/-- **etcd's no-leader error** (persistent): the value of `rpctypes.ErrGRPCNoLeader` (a status
error, `status.Error(codes.Unavailable, "etcdserver: no leader")`). -/
def noLeaderErr (err : GoInterface) : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ↦□ GoInterface.ok e ∗
    ⌜err = GoInterface.ok e⌝)

instance noLeaderErr_persistent (err : GoInterface) : Persistent (noLeaderErr (GF := GF) err) := by
  unfold noLeaderErr; infer_instance

/-- `ctxCauseOk`'s fact, raw (opaque). -/
opaque v3rpc.ctxCauseOkRaw (c : GoInterfaceOk) : IProp GF

/-- **The causes of the context `c` are context errors or etcd's no-leader error** (persistent,
opaque; TRUSTED; k8s 7f-4, Addendum T-k, decided by etcd-grove-81 with the user's approval,
2026-11-13). Its meaning in Go (go1.27.3 `src/context/context.go`), "a cause error" being `nil`,
`context.Canceled`'s value, `context.DeadlineExceeded`'s value or `rpctypes.ErrGRPCNoLeader`'s value:
* (i) the `cause` field of the `*cancelCtx` that `c.Value(&cancelCtxKey)` returns, if it returns one
  (the one `parentCancelCtx(c)` finds, then), holds only cause errors, at every time;
* (ii) a non-nil error `c.Err()` returns while that field holds `nil`, or when `c.Value(&cancelCtxKey)`
  returns no `*cancelCtx`, is a cause error;
so (iii) every call of `context.Cause(c)` (`c.Err()`; `nil` if it is; else the found `*cancelCtx`'s
`cause` if non-nil; else that error, `:289-307`) returns a cause error, and so does every cause a
context `context` makes over `c` stores (`propagateCancel`'s arms: `Cause(c)` when `c` is done, the found
`*cancelCtx`'s `cause` when it is cancelled, `:476-528, 550-575`); and a child made with a nil cause
(`WithCancel`, `WithTimeout`, `WithDeadline`) stores, of its own, its error as its cause (`Canceled` from
its cancel function, `DeadlineExceeded` from its timer). Not a child made by `WithCancelCause`,
`WithDeadlineCause` or `WithTimeoutCause`, which stores the caller's cause (`:269-271, 633-660, 711`).

It says nothing of whether those calls return (the context's own facts say that: `"#HErr"`,
`"#HValue"` of `ctxDoneErr`), only of the errors that come out. What it excludes: a context made by
`WithCancelCause`, `WithDeadlineCause` or `WithTimeoutCause` with another cause, or a context of the
program's own whose `Err()` returns another error with no `*cancelCtx` under it: `net/http`'s transport
returns `context.Cause` of its child of the request's context (go1.27.3 `net/http/transport.go:675, 698`),
so over such a context `RenewHTTP` returned an error whose `Is` method panics
(`notes/renewhttp-cause-refuted.md`, `TestRenewHTTPCausePanics`, `TestLeaseTimeToLiveFollowerCausePanics`).
Perennial's model does not track causes (`cancelCtxLockInv`'s `cause`, no fact), so no proof can derive
this; it is claimed where contexts are made and carried.

Given by: grpc's run model (`grpcRunCtx`, so `srvRawStreamIs`: grpc v1.84.0 and net/http's server make
their contexts with `WithCancel`, `WithTimeout` and `WithValue` only, never a cause variant), the law
`v3rpc.ctxCauseOk_cancellable` (etcd's `*cancellableContext`), `traceutil.Tracer.Start.spec`'s post
(`WithValue` links over `c`: one, or two with the SDK tracer and Go's execution tracer on; or `c`), and the local axiom `v3rpc.wp_WithTimeout_weak`'s post (the
`*timerCtx` over `c`). No other spec may give it. Taken by `leasehttp.RenewHTTP.spec` and
`EtcdServer.leaseTimeToLive.spec`. -/
def v3rpc.ctxCauseOk (c : GoInterfaceOk) : IProp GF := iprop(□ v3rpc.ctxCauseOkRaw c)

instance v3rpc.ctxCauseOk_persistent (c : GoInterfaceOk) :
    Persistent (v3rpc.ctxCauseOk (GF := GF) c) := by
  unfold v3rpc.ctxCauseOk; infer_instance

/-- **A stream handler's context** `c` described by `s` (persistent; k8s 7f-4, T-f): `isContext c s`
(`Perennial/Proof/context/Base.lean`, `isContextDef`) with its `Err()` clauses weakened:
* `"#HErr"`: `Err()` returns some error, nil or not, at any time (the Err-before-Done window:
  `issues/etcd-stream-interceptor-err-before-done.md`), the caller lending a level token
  (`levelTok v3rpc.ctxErrLvl`, returned: the wrapper's `Err` read-locks an `RWMutex`, whose reader
  slot a live thread pays for; Freeze addendum T-f');
* `"#HErrDone"`: once `Done` is closed (`ContextClosed s.Done_gn`), a non-nil error that is
  `Canceled`'s or `DeadlineExceeded`'s value (`isCtxErr`) or etcd's no-leader error
  (`noLeaderErr`), with the same level token lent and returned;
* the other clauses as `isContext`'s: `Deadline()` returns the descriptor's deadline, `Done()` the
  context's Done channel (`isContextDone`), `Value(&cancelCtxKey)` nothing or a valid `*cancelCtx`,
  the Done channel fresh (`"#HDoneFresh"`), `parentCancelCtx(c)` a valid `*cancelCtx`
  (`"#HParentCC"`), and `context`'s `isClosedchanInit`. -/
def srvCtxWeak (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : GoChan) (γch : ChanNames), context.isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    □ (∀ Φ : val → IProp GF, levelTok v3rpc.ctxErrLvl -∗
      ▷ (∀ err : GoInterface, levelTok v3rpc.ctxErrLvl -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : GoInterface, context.isCancelCtxAny v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #context.cancelCtxKeyAny)) {{ Φ }}) ∗
  "#HErrDone" ∷
    □ (∀ Φ : val → IProp GF, context.ContextClosed s.Done_gn -∗ levelTok v3rpc.ctxErrLvl -∗
      ▷ (∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ (context.isCtxErr err ∨ noLeaderErr err) -∗
        levelTok v3rpc.ctxErrLvl -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDoneFresh" ∷
    □ (∀ ch : GoChan, dghostVar s.Done_gn.doneGn .discard (some ch) ={⊤}=∗
      context.doneFreshT s.Done_gn ch) ∗
  "#HParentCC" ∷ (⌜c.ty ≠ _root_.Perennial.context.stopCtx.ty⌝ ∗
    □ (∀ (ch cch : GoChan) (Φ : val → IProp GF),
      dghostVar s.Done_gn.doneGn .discard (some ch) -∗
      globalAddr _root_.Perennial.context.closedchan ↦□ cch -∗ ⌜ch ≠ cch⌝ -∗
      ▷ (∀ p : Loc, context.isCancelCtx p -∗ Φ (PairV #p #true)) -∗
      WP (App (Val (@! _root_.Perennial.context.parentCancelCtx)) (Val #(interface.ok c))) {{ Φ }})) ∗
  "#HClosedchan" ∷ context.isClosedchanInit)

instance srvCtxWeak_persistent (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    Persistent (srvCtxWeak c s) := by
  unfold srvCtxWeak; infer_instance

/-- **A context whose `Done()` callers may take its `Err()`, and that `context` may use as a parent**
(persistent; k8s 7f-4, Addendum T-j; T-h2 with T-h5's option (A), decided by etcd-grove-81): what
`waitLeader` and `RenewHTTP` take of their context (`srvCtxWeak` and the child
`v3rpc.wp_WithTimeout_weak` makes both are one: `ctxDoneErr_of_srvCtxWeak`, `ctxDoneErr_of_child`).
`srvCtxWeak` with the two clauses that name Perennial's `isCancelCtx` stated over
`context.madeCancelCtx` instead (a `*cancelCtx` `context` made, of whatever stored error, where
`isCancelCtx`'s invariant has a context error, false of a child made over a done wrapper: T-h1):
* `"#HValue"`: `Value(&cancelCtxKey)` returns `nil`, a value of another dynamic type, or a
  `*cancelCtx` `context` made (`context.madeCancelCtxAny`); not any value (T-h2's `"#HValueAny"`,
  refuted: a nil `*cancelCtx` makes `RenewHTTP` panic, `TestRenewHTTPNilCancelCtxPanics`);
* `"#HParentCC"`: `c` is not a `stopCtx`, and `parentCancelCtx(c)` finds a `*cancelCtx` `context` made
  once the Done channel is known and is not `closedchan` (kept, unlike T-h2's text, which dropped it:
  without it, `propagateCancel` reaches its `afterFuncer` arm and calls the context's own `AfterFunc`,
  which may panic, `TestRenewHTTPAfterFuncPanics`, or its goroutine arm);
* the others as `srvCtxWeak`'s: `Deadline`, `Done`, `Err` (any error, the caller lending
  `levelTok v3rpc.ctxErrLvl`), `Err` after `Done` (non-nil, `isCtxErr ∨ noLeaderErr`, the token lent),
  the Done channel fresh, `isClosedchanInit`. -/
def v3rpc.ctxDoneErr (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : GoChan) (γch : ChanNames), context.isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    □ (∀ Φ : val → IProp GF, levelTok v3rpc.ctxErrLvl -∗
      ▷ (∀ err : GoInterface, levelTok v3rpc.ctxErrLvl -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : GoInterface, context.madeCancelCtxAny v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #context.cancelCtxKeyAny)) {{ Φ }}) ∗
  "#HErrDone" ∷
    □ (∀ Φ : val → IProp GF, context.ContextClosed s.Done_gn -∗ levelTok v3rpc.ctxErrLvl -∗
      ▷ (∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ (context.isCtxErr err ∨ noLeaderErr err) -∗
        levelTok v3rpc.ctxErrLvl -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDoneFresh" ∷
    □ (∀ ch : GoChan, dghostVar s.Done_gn.doneGn .discard (some ch) ={⊤}=∗
      context.doneFreshT s.Done_gn ch) ∗
  "#HParentCC" ∷ (⌜c.ty ≠ _root_.Perennial.context.stopCtx.ty⌝ ∗
    □ (∀ (ch cch : GoChan) (Φ : val → IProp GF),
      dghostVar s.Done_gn.doneGn .discard (some ch) -∗
      globalAddr _root_.Perennial.context.closedchan ↦□ cch -∗ ⌜ch ≠ cch⌝ -∗
      ▷ (∀ p : Loc, context.madeCancelCtx p -∗ Φ (PairV #p #true)) -∗
      WP (App (Val (@! _root_.Perennial.context.parentCancelCtx)) (Val #(interface.ok c))) {{ Φ }})) ∗
  "#HClosedchan" ∷ context.isClosedchanInit)

instance v3rpc.ctxDoneErr_persistent (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    Persistent (v3rpc.ctxDoneErr c s) := by
  unfold v3rpc.ctxDoneErr; infer_instance

/-- **The context `v3rpc.wp_WithTimeout_weak` makes** (persistent; k8s 7f-4, Addendum T-j; T-h2):
`ctxDoneErr`'s clauses with a `*timerCtx`'s `Err()`, which takes no `RWMutex` reader slot, so no level
token (an atomic load of its `err` cell, then `<-c.Done()`, which may briefly take its `mu`, a
`sync.Mutex`, or wait for the concurrent `cancel` to close `done`): `"#HErr"`, at any time `nil` or a context error or etcd's no-leader error (the
error its `cancel` stored: `Canceled` from its own cancel or its parent's inner `*cancelCtx`,
`DeadlineExceeded` from its timer, or the parent's `Err()` when the parent was already done,
`propagateCancel`'s first arm, T-h1); `"#HErrDone"`, after `Done` non-nil, one of those. -/
def v3rpc.ctxChildErr (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) : IProp GF :=
  iprop(
  "#HDeadline" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (True -∗ Φ (PairV #(s.Deadline.getD (zero_val time.Time))
                          #(match s.Deadline with | none => false | some _ => true))) -∗
      WP (App (Val #(methods c.ty go!"Deadline" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDone" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ (ch : GoChan) (γch : ChanNames), context.isContextDone s ch γch -∗ Φ #ch) -∗
      WP (App (Val #(methods c.ty go!"Done" c.v)) (Val #())) {{ Φ }}) ∗
  "#HErr" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ err : GoInterface,
        (⌜err = GoInterface.nil⌝ ∨ context.isCtxErr err ∨ noLeaderErr err) -∗ Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HValue" ∷
    □ (∀ Φ : val → IProp GF, True -∗
      ▷ (∀ v : GoInterface, context.madeCancelCtxAny v -∗ Φ #v) -∗
      WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #context.cancelCtxKeyAny)) {{ Φ }}) ∗
  "#HErrDone" ∷
    □ (∀ Φ : val → IProp GF, context.ContextClosed s.Done_gn -∗
      ▷ (∀ err : GoInterface, ⌜err ≠ GoInterface.nil⌝ -∗ (context.isCtxErr err ∨ noLeaderErr err) -∗
        Φ #err) -∗
      WP (App (Val #(methods c.ty go!"Err" c.v)) (Val #())) {{ Φ }}) ∗
  "#HDoneFresh" ∷
    □ (∀ ch : GoChan, dghostVar s.Done_gn.doneGn .discard (some ch) ={⊤}=∗
      context.doneFreshT s.Done_gn ch) ∗
  "#HParentCC" ∷ (⌜c.ty ≠ _root_.Perennial.context.stopCtx.ty⌝ ∗
    □ (∀ (ch cch : GoChan) (Φ : val → IProp GF),
      dghostVar s.Done_gn.doneGn .discard (some ch) -∗
      globalAddr _root_.Perennial.context.closedchan ↦□ cch -∗ ⌜ch ≠ cch⌝ -∗
      ▷ (∀ p : Loc, context.madeCancelCtx p -∗ Φ (PairV #p #true)) -∗
      WP (App (Val (@! _root_.Perennial.context.parentCancelCtx)) (Val #(interface.ok c))) {{ Φ }})) ∗
  "#HClosedchan" ∷ context.isClosedchanInit)

instance v3rpc.ctxChildErr_persistent (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    Persistent (v3rpc.ctxChildErr c s) := by
  unfold v3rpc.ctxChildErr; infer_instance

/-- **A context is a weak one** (the contract's first law). -/
theorem srvCtxWeak_of_isContext (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    context.isContext c s ⊢ srvCtxWeak c s := by
  iintro #H
  unfold context.isContext context.isContextDef
  icases H with ⟨#HDeadline, #HDone, #HErr, #HValue, #HErrDone, #HDoneFresh, #HParentCC, #Hcci⟩
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  unfold srvCtxWeak
  iframe #
  isplitl []
  · iintro !> %Φ Ht HΦ
    iapply HErrU $$ []
    · itrivial
    iintro !> %err - -
    iapply HΦ $$ Ht
  iintro !> %Φ #Hcl Ht HΦ
  iapply HErrDone $$ Hcl
  iintro !> %err %Hty #He
  iapply HΦ $$ [] [] Ht
  · ipureintro; exact context.isTypedErr_ne_nil Hty
  ileft; iexact He

/-- **A weak context is a `ctxDoneErr`** (by `context.madeCancelCtx_of_isCancelCtx`). -/
theorem v3rpc.ctxDoneErr_of_srvCtxWeak (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    srvCtxWeak c s ⊢ v3rpc.ctxDoneErr c s := by
  iintro #H
  unfold srvCtxWeak
  icases H with ⟨#HDeadline, #HDone, #HErr, #HValue, #HErrDone, #HDoneFresh, ⟨%Hty, #HParentCC⟩, #Hcci⟩
  unfold v3rpc.ctxDoneErr
  iframe #
  isplitl []
  · iintro !> %Φ - HΦ
    iapply HValue $$ []
    · itrivial
    iintro !> %v #Hv
    iapply HΦ
    iapply context.madeCancelCtxAny_of_isCancelCtxAny
    iexact Hv
  isplitr
  · ipureintro; exact Hty
  iintro !> %ch %cch %Φ Hd Hcc %Hne HΦ
  iapply HParentCC $$ Hd Hcc
  · ipureintro; exact Hne
  iintro !> %p #Hp
  iapply HΦ
  iapply context.madeCancelCtx_of_isCancelCtx
  iexact Hp

/-- **A context is a `ctxDoneErr`.** -/
theorem v3rpc.ctxDoneErr_of_isContext (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    context.isContext c s ⊢ v3rpc.ctxDoneErr c s := by
  iintro #H
  iapply v3rpc.ctxDoneErr_of_srvCtxWeak
  iapply srvCtxWeak_of_isContext
  iexact H

/-- **The child `v3rpc.wp_WithTimeout_weak` makes is a `ctxDoneErr`** (its `Err` needs no token: the
caller's is passed through). -/
theorem v3rpc.ctxDoneErr_of_child (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    v3rpc.ctxChildErr c s ⊢ v3rpc.ctxDoneErr c s := by
  iintro #H
  unfold v3rpc.ctxChildErr
  icases H with ⟨#HDeadline, #HDone, #HErr, #HValue, #HErrDone, #HDoneFresh, #HParentCC, #Hcci⟩
  unfold v3rpc.ctxDoneErr
  iframe #
  isplitl []
  · iintro !> %Φ Ht HΦ
    iapply HErr $$ []
    · itrivial
    iintro !> %err -
    iapply HΦ $$ Ht
  iintro !> %Φ #Hcl Ht HΦ
  iapply HErrDone $$ Hcl
  iintro !> %err %Hne #He
  iapply HΦ $$ [] He Ht
  ipureintro; exact Hne

/-- **A weak context's `Done()` is one the auth store may select on** (T-e'). -/
theorem auth.ctxDoneAny_of_srvCtxWeak (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) :
    srvCtxWeak c s ⊢ auth.ctxDoneAny c := by
  iintro #H
  unfold auth.ctxDoneAny
  iintro !> %Φ !> - HΦ
  unfold srvCtxWeak
  icases H with ⟨-, #HDone, -⟩
  iapply HDone $$ []
  · itrivial
  iintro !> %ch %γch Hd
  iapply HΦ
  iright
  iexists s, γch
  iexact Hd

end defs

end EtcdGrove
end Perennial
