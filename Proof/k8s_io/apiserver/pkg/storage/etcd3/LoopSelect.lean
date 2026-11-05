/-
**The compactor loop's `select`** (`compact.go`, `runCompactLoop`: `select { case
<-c.clock.After(c.interval): case <-ctx.Done(): return }`; K4 of `notes/k8s-compactor-plan.md`).
Lean-first. A blocking `select` between a timer's channel (`isChanBag`, `RealClock.After`'s) and a
broadcast channel (the stop channel, `ctx.Done()` of `wait.ContextForChannel(stop)`): the timer's
case with some time, or the stop channel's once it is closed. As client-go's `wp_select_done_bag`
(`RefCtx.lean`), in the other case order and over a broadcast channel.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [time_sem : time.Assumptions]

theorem wp_select_bag_stop (ach : Loc) (γa : ChanNames) (sc : GoChan) (γs : ChanNames)
    (Q : IProp GF) (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := time.Time) γa ach (fun _ => iprop(True)) -∗
      ownBroadcastChan sc γs Q .Unknown -∗ £ 1 ∗ £ 1 -∗
      ((∀ t : time.Time, WP (App h1 (Val (PairV #t #true))) {{ Φ }}) ∧
        WP (App h2 (Val (PairV #() #false))) {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase time.Time.ty (Val #ach)) h1,
         CommClause (RecvCase (go.StructType []) (Val #sc)) h2]))) {{ Φ }} := by
  iintro #Hb #Hs Hlc Hh
  iapply chan.wp_select_blocking
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
    icases Hh with ⟨Hh, -⟩
    iapply Hh
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sc, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hs
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hs
    iintro -
    icases Hh with ⟨-, Hh⟩
    iexact Hh
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
