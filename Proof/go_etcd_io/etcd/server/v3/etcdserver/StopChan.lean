/-
**A buffered channel closed once and never sent on** (the server's `stopping`: `start` makes it
with `make(chan struct{}, 1)`; `run`'s deferred shutdown closes it; the read loop, `GoAttach` and
the monitors only receive from it). Lean-first (the request path's unit 4c, 2026-10-13).

Perennial's broadcast idiom (`Perennial/Golang/Theory/Chan/Idioms/Broadcast.lean`: a channel
never sent on, closed once, the close telling a persistent `Q`) is stated for an unbuffered
channel: its invariant's open states are `.Idle`/`.RcvPending`, and its allocation takes the
`.Idle` a `make(chan T)` returns. A `make(chan T, 1)` starts at `.Buffered []`, and with no send
it stays there until the close (`.Closed []`): this file states the same idiom over those two
states (`ownStopChan`, the receive, non-blocking receive and close rules, the allocation from a
`make2`), without changing Perennial. A blocking receive on the open channel does not commit (its
atomic update's `.Buffered []` case is the "not ready" one); on the closed one it returns the zero
value and `Q`.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The invariant of a buffered channel never sent on: empty and open (the closer's half of the
done flag elsewhere), or closed and drained (`□ Q`, the flag discarded). -/
def stopChanInv (γ : ChanNames) (γch : BroadcastInternalNames) (Q : IProp GF) : IProp GF :=
  iprop(∃ (st : ChanState Unit),
    "Hch" ∷ ownChan γ Unit st ∗
    "Hs" ∷ (match st with
      | .Buffered [] => dghostVar γch.doneGn (.own (1 : Qp).half) false
      | .Closed [] => iprop(□ Q ∗ dghostVar γch.doneGn .discard true)
      | _ => iprop(False)))

/-- The channel and its invariant (persistent). -/
def isStopChanInternal (ch : GoChan) (γ : ChanNames) (γch : BroadcastInternalNames)
    (Q : IProp GF) : IProp GF :=
  iprop("#His_ch" ∷ isChan ch γ Unit ∗ "#Hinv" ∷ inv (nroot.@"stopchan") (stopChanInv γ γch Q))

instance isStopChanInternal_pers (ch : GoChan) γ γch (Q : IProp GF) :
    Persistent (isStopChanInternal ch γ γch Q) := by
  unfold isStopChanInternal; infer_instance

/-- **The channel `ch`, closed once and never sent on, closing with `Q`**: the closer's view
(`.Pending`, not closed yet), a receiver's that saw it closed (`.Done`), anyone's (`.Unknown`,
persistent). -/
def ownStopChan (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (st : Broadcast) : IProp GF :=
  iprop(∃ γch,
    "#Hinv" ∷ isStopChanInternal ch γ γch Q ∗
    "Hown" ∷ (match st with
      | .Pending => dghostVar γch.doneGn (.own (1 : Qp).half) false
      | .Done => dghostVar γch.doneGn .discard true
      | .Unknown => iprop(True)))

instance ownStopChan_Unknown_pers (ch : GoChan) γ (Q : IProp GF) :
    Persistent (ownStopChan ch γ Q .Unknown) := by
  unfold ownStopChan; infer_instance

instance ownStopChan_Done_pers (ch : GoChan) γ (Q : IProp GF) :
    Persistent (ownStopChan ch γ Q .Done) := by
  unfold ownStopChan; infer_instance

/-- **A receiver's view of `ch`** (persistent): closed once, never sent on, no content. -/
def stopChan (ch : GoChan) : IProp GF :=
  iprop(∃ γ : ChanNames, ownStopChan ch γ iprop(True) .Unknown)

instance stopChan_persistent (ch : GoChan) : Persistent (stopChan (GF := GF) ch) := by
  unfold stopChan; infer_instance

theorem ownStopChan_is_chan (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (cl : Broadcast) :
    ⊢ ownStopChan ch γ Q cl -∗ isChan ch γ Unit := by
  unfold ownStopChan isStopChanInternal
  iintro ⟨%γch, ⟨#His_ch, -⟩, -⟩
  iexact His_ch

theorem ownStopChan_Unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (cl : Broadcast) :
    ⊢ ownStopChan ch γ Q cl -∗ ownStopChan ch γ Q .Unknown := by
  unfold ownStopChan
  iintro ⟨%γch, #Hint, -⟩
  iexists γch
  iframe Hint

/-- The closer's view gives a receiver's too. -/
theorem ownStopChan_pending_unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    ownStopChan ch γ Q .Pending ⊢ ownStopChan ch γ Q .Pending ∗ ownStopChan ch γ Q .Unknown := by
  unfold ownStopChan
  iintro ⟨%γch, #Hint, Hd⟩
  isplitl [Hd]
  · iexists γch; iframe Hint Hd
  · iexists γch; iframe Hint

/-- **Allocation**: a fresh `make(chan struct{}, 1)` (`.Buffered []`). -/
theorem alloc_stop_chan {E : CoPset} (Q : IProp GF) (γ : ChanNames) (ch : GoChan) :
    ⊢ isChan ch γ Unit -∗ ownChan γ Unit (.Buffered []) ={E}=∗ ownStopChan ch γ Q .Pending := by
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%tok_gn, Htok⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Htok] with ⟨Htok, Htok2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Htok
  imod inv_alloc (nroot.@"stopchan") E (stopChanInv γ ⟨tok_gn⟩ Q) $$ [Hoc Htok2] with #Hinv
  · inext; unfold stopChanInv; iexists .Buffered []; dsimp only; iframe
  imodintro
  unfold ownStopChan isStopChanInternal
  iexists ⟨tok_gn⟩
  dsimp only
  iframe Htok
  unfold named
  isplit <;> iassumption

/-- **A (blocking) receive**: it commits only once the channel is closed, with the zero value and
`□ Q`. -/
theorem stop_chan_receive (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (cl : Broadcast) :
    ⊢ ownStopChan ch γ Q cl -∗
      (□ Q ∗ ownStopChan ch γ Q .Done -∗ Φ () false) -∗
      recvAu γ Unit Φ := by
  unfold ownStopChan isStopChanInternal recvAu
  iintro ⟨%γch, ⟨#His_ch, #Hinv⟩, Hown⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Closed.nil =>
    iintro Hch
    icases Hs with ⟨#HQ, #Hs⟩
    imod Hmask with -
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iapply HΦ
    isplitl []
    · imodintro; iexact HQ
    iexists γch
    isplitl []
    · isplitl []
      · iexact His_ch
      · iexact Hinv
    · iexact Hs
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- **A non-blocking receive** (a `select` with a `default`): the zero value and the done view
once closed, else not ready (the view kept). -/
theorem stop_chan_nonblocking_receive (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) (cl : Broadcast) :
    ⊢ ownStopChan ch γ Q cl -∗
      ((match cl with
        | .Unknown | .Done => iprop(□ Q ∗ ownStopChan ch γ Q .Done -∗ Φ () false)
        | _ => iprop(True)) ∧
       (match cl with
        | .Unknown | .Pending => iprop(ownStopChan ch γ Q cl -∗ Φnotready)
        | _ => iprop(True))) -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro Hown HΦ
  unfold ownStopChan
  icases Hown with ⟨%γch, #Hint, Hown⟩
  ihave #Hint' := Hint
  unfold isStopChanInternal
  icases Hint' with ⟨#His_ch, #Hinv⟩
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .Buffered []; dsimp only; iframe
      imodintro
      iapply HΦ
      iexists γch
      iframe Hint
      try iframe
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Pending =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨HΦ, -⟩
      imod Hclose $$ [Hch] with -
      · inext; iexists .Closed []; dsimp only; iframe Hch
        isplitl []
        · imodintro; iexact HQ
        · iexact Hs
      imodintro
      iapply HΦ
      isplitl []
      · imodintro; iexact HQ
      iexists γch
      iframe Hint Hs
  all_goals (iexfalso; iexact Hs)

/-- **The close**, by the closer, with `□ Q`. -/
theorem stop_close_au (ch : GoChan) (γch : ChanNames) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ ownStopChan ch γch Q .Pending -∗ □ Q -∗
      ▷ (ownStopChan ch γch Q .Done -∗ Φ) -∗ closeAu γch Unit Φ := by
  iintro Hown #HQ HΦ
  unfold ownStopChan
  icases Hown with ⟨%γi, #Hint, Hown⟩
  ihave #Hint' := Hint
  unfold isStopChanInternal
  icases Hint' with ⟨#His_ch, #Hinv⟩
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hch
    imod Hmask with -
    imod dghostVar_update_halves true _ _ _ $$ Hown Hs with ⟨Hown, -⟩
    imod dghostVar_persist _ _ _ $$ Hown with #Hown
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hown
    imodintro
    iapply HΦ
    iexists γi
    iframe Hint Hown
  case Closed.nil =>
    icases Hs with ⟨-, #Hs⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

/-- **A non-blocking receive by a holder of a fraction of the closer's flag** (`own q`, `false`:
`GoAttach` under the read lock of `wgMu`, whose resource holds such fractions while the channel is
open): the channel is open, the receive is not ready, the fraction comes back. -/
theorem stop_chan_nonblocking_receive_open (ch : GoChan) (γ : ChanNames)
    (γch : BroadcastInternalNames) (Q : IProp GF) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) (q : Qp) :
    ⊢ isStopChanInternal ch γ γch Q -∗ dghostVar γch.doneGn (.own q) false -∗
      (dghostVar γch.doneGn (.own q) false -∗ Φnotready) -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro #Hint Hown HΦ
  ihave #Hint' := Hint
  unfold isStopChanInternal
  icases Hint' with ⟨#His_ch, #Hinv⟩
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.nil =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .Buffered []; dsimp only; iframe
    imodintro
    iapply HΦ $$ Hown
  case Closed.nil =>
    icases Hs with ⟨-, #Hs⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  all_goals (iexfalso; iexact Hs)

/-- **A non-blocking receive once closed** (the closer's flag discarded at `true`): it is ready,
with the zero value. -/
theorem stop_chan_nonblocking_receive_done (ch : GoChan) (γ : ChanNames)
    (γch : BroadcastInternalNames) (Q : IProp GF) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) :
    ⊢ isStopChanInternal ch γ γch Q -∗ dghostVar γch.doneGn .discard true -∗ Φ () false -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro #Hint #Hown HΦ
  ihave #Hint' := Hint
  unfold isStopChanInternal
  icases Hint' with ⟨#His_ch, #Hinv⟩
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold stopChanInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Buffered.nil =>
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hs Hown
    cases Hbad
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iexact HΦ
  all_goals (iexfalso; iexact Hs)

end proof

end EtcdGrove
end Perennial
