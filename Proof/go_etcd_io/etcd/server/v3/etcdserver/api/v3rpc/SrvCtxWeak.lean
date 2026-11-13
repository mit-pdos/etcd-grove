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
