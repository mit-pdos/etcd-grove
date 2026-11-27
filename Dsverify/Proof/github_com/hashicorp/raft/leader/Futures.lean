/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/Futures.lean (241f27e).
-/
/-
The leader part of the main goroutine (agent MAIN-L), stage 2: the `deferError` methods called
through the stage-2 future types (the frozen `deferError.respond`/`init` specs are stated through
`*logFuture`): `respond` on a `*verifyFuture` and a `*leadershipTransferFuture`, and `init` on a
bare `*deferError` (the transfer goroutine's replication requests). Proved directly (the methods'
code: a send on the answer channel and its close).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.leader.Defs
public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft gprot proto

/-- `deferError.respond`'s body on the `deferError` at `de` (whatever embeds it). -/
theorem wp_respond_body (de : Loc) (Q : GoInterface → IProp GF) (err : GoInterface)
    (Φ : val → IProp GF) :
    ((deferResp de Q ∗ Q err) ∨ deferDone de) -∗ ▷ (deferDone de -∗ Φ #()) -∗
    WP (App (Val (de @!! go.GoType.PointerType deferError.ty @!! go!"respond")) (Val #err)) {{ Φ }} := by
  iintro Hpre HΦ
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

/-- `respond(err)` on a `*verifyFuture` (promoted from its `deferError`). -/
theorem wp_verifyFuture_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       ((deferResp (f.[verifyFuture, go!"deferError"]) Q ∗ Q err) ∨
        deferDone (f.[verifyFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone (f.[verifyFuture, go!"deferError"]) }} := by
  wp_start_folded as Hpre
  wp_method_call
  wp_auto
  iapply wp_respond_body $$ Hpre HΦ

/-- `respond(err)` on a `*leadershipTransferFuture` (promoted from its `deferError`). -/
theorem wp_ltFuture_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       ((deferResp (f.[leadershipTransferFuture, go!"deferError"]) Q ∗ Q err) ∨
        deferDone (f.[leadershipTransferFuture, go!"deferError"])) }}
      (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"respond")) (Val #err))
    {{ RET #(); deferDone (f.[leadershipTransferFuture, go!"deferError"]) }} := by
  wp_start_folded as Hpre
  wp_method_call
  wp_auto
  iapply wp_respond_body $$ Hpre HΦ

/-- `init()` on a bare `*deferError` (the transfer goroutine's replication requests): makes the
answer channel for an answer predicate `Q`, its producer and consumer sides. -/
theorem wp_deferError_init (de : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
       de.[deferError, go!"errCh"] ↦ ch0 }}
      (App (Val (de @!! go.GoType.PointerType deferError.ty @!! go!"init")) (Val #()))
    {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      de.[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

/-- A fresh stop channel (`chan uint64`, capacity 1, nothing sent) as the broadcast stop channel of
a replication goroutine, with the right to close it. -/
theorem stopChan_alloc (ch : Loc) (γc : ChanNames) :
    isChan ch γc w64 ∗ ownChan γc w64 (ChanState.Buffered ([] : List w64)) ⊢ |={⊤}=>
      ∃ γs : StopNames, stopChan (GF := GF) γs ch ∗ stopCloser γs := by
  iintro ⟨#Hch, Hown⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%γd, Hd⟩
  imod dghostVar_alloc (GF := GF) false with ⟨%γn, Hn⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Hd] with ⟨Hd1, Hd2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hd
  imod inv_alloc stopN ⊤ (stopInv ⟨γc, γd, γn⟩) $$ [Hown Hd1] with #Hinv
  · inext; unfold stopInv; iexists (ChanState.Buffered []); iframe
  imodintro
  iexists ⟨γc, γd, γn⟩
  unfold stopChan stopCloser stopSendTok
  iframe; iframe #

/-- (review tier-2 5) `stopCh <- lastIdx` (`startStopReplication` stops a removed server's
goroutine): the main goroutine, holding the send token, finds the buffer empty and the channel open
(it holds the closer's half), so the send does not block; the token goes into the buffer. -/
theorem wp_stop_send (γs : StopNames) (ch : Loc) (v : w64) :
    {{ stopChan (GF := GF) γs ch ∗ stopCloser γs }}
      (App (App (Val (chan.send go.uint64)) (Val #ch)) (Val #v))
    {{ RET #(); stopCloseRight γs }} := by
  iintro %Φ ⟨Hst, Hcl⟩ HΦ
  unfold stopChan stopCloser
  icases Hst with ⟨#Hch, #Hinv⟩
  icases Hcl with ⟨Hcl, Htok⟩
  iapply chan.wp_send (V := w64) ch v γs.ch $$ Hch
  iintro -
  unfold sendAu
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopInv
  icases Hi with ⟨%st, Hoc, Hs⟩
  iexists st
  iframe Hoc
  rcases st with (_ | ⟨_, (_ | ⟨_, _⟩)⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, (_ | ⟨_, _⟩)⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hs Htok] with -
    · inext; iexists (ChanState.Buffered [v]); dsimp only; unfold stopSendTok; iframe
    imodintro
    iapply HΦ; unfold stopCloseRight; iexact Hcl
  case Buffered.cons.nil =>
    icases Hs with ⟨-, Htok'⟩
    unfold stopSendTok
    ihave %Hv := dghostVar_valid_2 _ _ _ _ _ $$ Htok Htok'
    exact absurd (DFrac.valid_op_own Hv.1) (by simp)
  case Closed.nil =>
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
    cases Hbad
  case Closed.cons.nil =>
    icases Hs with ⟨Hs, -⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- (review tier-2 5) The closer may give up its send (the leader steps down: `close` only). -/
theorem stopCloser_close (γs : StopNames) : stopCloser (GF := GF) γs ⊢ stopCloseRight γs := by
  unfold stopCloser stopCloseRight
  iintro ⟨H, -⟩
  iexact H

/-- `close(stopCh)` (the leader steps down): the stop channel's closer closes it, once. (Review
tier-2 5: the pre is the close right without the send token, `stopCloser_close`.) -/
theorem wp_stop_close (γs : StopNames) (ch : Loc) :
    {{ stopChan (GF := GF) γs ch ∗ stopCloseRight γs }}
      (App (Val #(functions go.close [go.GoType.ChannelType go.ChanDir.sendrecv go.uint64])) (Val #ch))
    {{ RET #(); True }} := by
  iintro %Φ ⟨Hst, Hcl⟩ HΦ
  unfold stopChan stopCloseRight
  icases Hst with ⟨#Hch, #Hinv⟩
  iapply chan.wp_close (V := w64) ch γs.ch $$ Hch
  iintro -
  unfold closeAu
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopInv
  icases Hi with ⟨%st, Hoc, Hs⟩
  iexists st
  iframe Hoc
  rcases st with (_ | ⟨_, (_ | ⟨_, _⟩)⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, (_ | ⟨_, _⟩)⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hoc
    imod Hmask with -
    imod dghostVar_update_halves true _ _ _ $$ Hcl Hs with ⟨Hcl, -⟩
    imod dghostVar_persist _ _ _ $$ Hcl with #Hcl
    imod Hclose $$ [Hoc] with -
    · inext; iexists (ChanState.Closed []); dsimp only; iframe; iframe #
    imodintro
    iapply HΦ; itrivial
  case Buffered.cons.nil =>
    iintro Hoc
    imod Hmask with -
    icases Hs with ⟨Hs, Htok⟩
    imod dghostVar_update_halves true _ _ _ $$ Hcl Hs with ⟨Hcl, -⟩
    imod dghostVar_persist _ _ _ $$ Hcl with #Hcl
    imod Hclose $$ [Hoc Htok] with -
    · inext; iexists (ChanState.Closed [_]); dsimp only; iframe; iframe #
    imodintro
    iapply HΦ; itrivial
  case Closed.nil =>
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
    cases Hbad
  case Closed.cons.nil =>
    icases Hs with ⟨Hs, -⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

end proof

end Perennial
