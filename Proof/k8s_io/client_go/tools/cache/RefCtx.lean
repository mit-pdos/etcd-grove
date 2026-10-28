/-
**The reflector's context** (phase 4 of `notes/k8s-daemonset-plan.md`, fifth round). Lean-first.

The reflector's goroutine runs under one context (`Reflector.RunWithContext(ctx)`, the informer's:
in `Main` `wait.ContextForChannel(stopCh)` of the factory's stop channel, whose `Done()` returns
`stopCh` each time). Its functions select on `ctx.Done()` many times, and a later `select` must take
the `Done` case once an earlier one did: `list` returns on `ctx.Done()` while its listing goroutine
still holds the reflector's fields, and the next `select` (`watch`'s) must then return too. Perennial's
`isContext` cannot say that (each `Done()` call returns the channel with fresh channel names), so the
reflector's specs take a context whose `Done()` is one channel (`stableCtx`), with its `isContext`
where a callee needs it (`context.WithCancel`).

* `stableCtx ctx ch γch`: `ctx.Done()` returns `ch`; `ch` is a broadcast channel (its proposition
  existential, unused) or the closed `closedchan`; once a receive on it returned (`ctxSeen`),
  `ctx.Err()` returns an error.
* `ctxSeen ch γch` (persistent): a receive on `ch` returned, so it is closed: a later receive, or a
  non-blocking one, returns at once (`ctxSeen_nb_recv`: the `select`'s default is not taken).
-/
module

public import Perennial.Proof.context.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **The `Done` channel has been seen closed** (persistent). -/
def ctxSeen (ch : GoChan) (γch : ChanNames) : IProp GF :=
  iprop((∃ Q : IProp GF, ownBroadcastChan ch γch Q .Done) ∨
    (isChan ch γch Unit ∗ inv context.closedchanN (ownChan γch Unit (.Closed []))))

instance ctxSeen_persistent (ch : GoChan) (γch : ChanNames) :
    Persistent (ctxSeen (GF := GF) ch γch) := by
  unfold ctxSeen; infer_instance

/-- **A context with one `Done` channel** (persistent): `ctx.Done()` returns `ch`, a broadcast
channel or the closed `closedchan`; once `ch` is seen closed, `ctx.Err()` returns an error. -/
def stableCtx (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames) : IProp GF :=
  iprop(□ (∀ Φ : val → IProp GF, ▷ Φ #ch -∗
      WP (App (Val #(methods ctx.ty go!"Done" ctx.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ Φ : val → IProp GF, ctxSeen ch γch -∗ ▷ (∀ err : GoInterface, ⌜err ≠ interface.nil⌝ -∗ Φ #err) -∗
      WP (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #())) {{ Φ }}) ∗
    ((∃ Q : IProp GF, ownBroadcastChan ch γch Q .Unknown) ∨
      (isChan ch γch Unit ∗ inv context.closedchanN (ownChan γch Unit (.Closed [])))))

instance stableCtx_persistent (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames) :
    Persistent (stableCtx (GF := GF) ctx ch γch) := by
  unfold stableCtx; infer_instance

theorem stableCtx_is_chan (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames) :
    stableCtx (GF := GF) ctx ch γch ⊢ isChan ch γch Unit := by
  unfold stableCtx
  iintro ⟨-, -, (⟨%Q, #Hbc⟩ | ⟨#Hch, -⟩)⟩
  · iapply ownBroadcastChan_is_chan $$ Hbc
  · iexact Hch

theorem ctxSeen_is_chan (ch : GoChan) (γch : ChanNames) :
    ctxSeen (GF := GF) ch γch ⊢ isChan ch γch Unit := by
  unfold ctxSeen
  iintro (⟨%Q, #Hbc⟩ | ⟨#Hch, -⟩)
  · iapply ownBroadcastChan_is_chan $$ Hbc
  · iexact Hch

/-- **A blocking receive on the `Done` channel** returns only once it is closed: then it is seen. -/
theorem stableCtx_recv (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames)
    (Φ : Unit → Bool → IProp GF) :
    ⊢ stableCtx ctx ch γch -∗ (ctxSeen ch γch -∗ Φ () false) -∗ recvAu γch Unit Φ := by
  unfold stableCtx
  iintro ⟨-, -, (⟨%Q, #Hbc⟩ | ⟨#Hch, #Hinv⟩)⟩ HΦ
  · iapply broadcast_chan_receive _ _ _ _ _ $$ Hbc
    iintro ⟨-, #Hd⟩
    iapply HΦ
    unfold ctxSeen
    ileft
    iexists Q
    iexact Hd
  · iapply context.closed_chan_receive $$ Hinv
    iapply HΦ
    unfold ctxSeen
    iright
    iframe #

/-- **A non-blocking receive on the `Done` channel**: it may be not ready, or it returns once the
channel is closed, which is then seen. -/
theorem stableCtx_nb_recv (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) :
    ⊢ stableCtx ctx ch γch -∗ ((ctxSeen ch γch -∗ Φ () false) ∧ Φnotready) -∗
      nonblockingRecvAuAlt γch Unit Φ Φnotready := by
  unfold stableCtx
  iintro ⟨-, -, (⟨%Q, #Hbc⟩ | ⟨#Hch, #Hinv⟩)⟩ HΦ
  · iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hbc
    dsimp only
    isplit
    · iintro #Hd
      icases HΦ with ⟨HΦ, -⟩
      iapply HΦ
      unfold ctxSeen
      ileft
      iexists Q
      iexact Hd
    · iintro -
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ
  · iapply context.closed_chan_nonblocking_receive $$ Hinv
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ
    unfold ctxSeen
    iright
    iframe #

/-- **A non-blocking receive on a channel seen closed** returns at once (its not-ready branch is
never taken: any `Φnotready`). -/
theorem ctxSeen_nb_recv (ch : GoChan) (γch : ChanNames) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) :
    ⊢ ctxSeen ch γch -∗ Φ () false -∗ nonblockingRecvAuAlt γch Unit Φ Φnotready := by
  iintro #Hs HΦ
  iunfold ctxSeen at Hs
  icases Hs with (⟨%Q, #Hd⟩ | ⟨#Hch, #Hinv⟩)
  · iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hd
    dsimp only
    isplit
    · iintro -
      iexact HΦ
    · itrivial
  · iapply context.closed_chan_nonblocking_receive $$ Hinv
    iexact HΦ

/-- **A blocking receive on a channel seen closed** returns at once. -/
theorem ctxSeen_recv (ch : GoChan) (γch : ChanNames) (Φ : Unit → Bool → IProp GF) :
    ⊢ ctxSeen ch γch -∗ Φ () false -∗ recvAu γch Unit Φ := by
  iintro #Hs HΦ
  iunfold ctxSeen at Hs
  icases Hs with (⟨%Q, #Hd⟩ | ⟨#Hch, #Hinv⟩)
  · iapply broadcast_chan_receive _ _ _ _ _ $$ Hd
    iintro -
    iexact HΦ
  · iapply context.closed_chan_receive $$ Hinv
    iexact HΦ

/-- **A non-blocking `select` on a `Done` channel seen closed** (`select { case <-done: ...;
default: ... }`): its case runs. -/
theorem wp_select_seen (ch : GoChan) (γch : ChanNames) (handler dflt : Expr) (Φ : val → IProp GF) :
    ⊢ ctxSeen ch γch -∗ WP (App handler (Val (PairV #() #false))) {{ Φ }} -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt)
        [CommClause (RecvCase (go.StructType []) (Val #ch)) handler]))) {{ Φ }} := by
  iintro #Hs Hh
  iapply chan.wp_select_nonblocking_alt [iprop(False)]
    iprop(WP (App handler (Val (PairV #() #false))) {{ Φ }}) $$ [] Hh
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro Hh
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ctxSeen_is_chan $$ Hs
    iapply ctxSeen_nb_recv $$ Hs
    iexact Hh
  · iintro - Hnr
    iexfalso
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ (P : IProp GF) => P)).1 $$ Hnr

/-- **A non-blocking `select` on the `Done` channel**: its case runs once the channel is seen
closed, or its default. -/
theorem wp_select_stable (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames) (handler dflt : Expr)
    (Φ : val → IProp GF) :
    ⊢ stableCtx ctx ch γch -∗
      ((ctxSeen ch γch -∗ WP (App handler (Val (PairV #() #false))) {{ Φ }}) ∧ WP dflt {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt)
        [CommClause (RecvCase (go.StructType []) (Val #ch)) handler]))) {{ Φ }} := by
  iintro #Hc Hh
  iapply chan.wp_select_nonblocking_alt [iprop(True)]
    iprop((ctxSeen ch γch -∗ WP (App handler (Val (PairV #() #false))) {{ Φ }}) ∧ WP dflt {{ Φ }})
    $$ [] Hh
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro Hh
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply stableCtx_is_chan $$ Hc
    iapply stableCtx_nb_recv $$ Hc
    isplit
    · iintro #Hs
      icases Hh with ⟨Hh, -⟩
      iapply Hh $$ Hs
    · iframe
  · iintro Hh -
    icases Hh with ⟨-, Hh⟩
    iexact Hh

/-- **A receive on a channel nothing is ever sent on and never closed** (its state `Buffered []`
for good, in an invariant) never returns: any continuation. -/
theorem never_recv_au {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] [Pos.Countable V]
    (N : Namespace) (γ : ChanNames) (Φ : V → Bool → IProp GF) :
    ⊢ inv N (ownChan γ V (.Buffered [])) -∗ recvAu γ V Φ := by
  iintro #Hinv
  unfold recvAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  inext
  iexists .Buffered []
  iframe Hi

/-- **A blocking `select` between the `Done` channel and a timer's channel** (`select { case
<-done: ...; case <-clock.After(d): ... }`): its first case once the `Done` channel is seen closed,
or its second with some time. -/
theorem wp_select_done_bag (ctx : GoInterfaceOk) (ch : GoChan) (γch : ChanNames) (ach : Loc)
    (γa : ChanNames) (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ stableCtx ctx ch γch -∗ isChanBag (V := time.Time) γa ach (fun _ => iprop(True)) -∗
      £ 1 ∗ £ 1 -∗
      ((ctxSeen ch γch -∗ WP (App h1 (Val (PairV #() #false))) {{ Φ }}) ∧
        (∀ t : time.Time, WP (App h2 (Val (PairV #t #true))) {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase (go.StructType []) (Val #ch)) h1,
         CommClause (RecvCase time.Time.ty (Val #ach)) h2]))) {{ Φ }} := by
  iintro #Hc #Hb Hlc Hh
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply stableCtx_is_chan $$ Hc
    iapply stableCtx_recv $$ Hc
    iintro #Hs
    icases Hh with ⟨Hh, -⟩
    iapply Hh $$ Hs
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, ach, γa
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb
    iapply bag_recv_au $$ Hlc Hb
    inext
    iintro %t -
    icases Hh with ⟨-, Hh⟩
    iapply Hh
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end defs

end cache
end EtcdGrove
end Perennial
