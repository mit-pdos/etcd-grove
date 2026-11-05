/-
**A broadcast channel through its internal names** (2026-11-04, K4 of
`notes/k8s-compactor-plan.md`: `channelContext.Err`'s `select`). Lean-first.

Perennial's broadcast idiom (`Perennial/Golang/Theory/Chan/Idioms/Broadcast.lean`) hides the done
flag's names in `ownBroadcastChan`'s existential, so a receive that finds the channel closed gives
`ownBroadcastChan .Done` with names unrelated to any the caller holds. A context built on the
channel needs its closed flag to be the channel's (`ContextClosed` exactly when the channel is
closed), so this file states the non-blocking receive at fixed internal names `γi`
(`isBroadcastChanInternal`): closed, it gives `dghostVar γi.doneGn .discard true`; given that flag,
it is closed. Without changing Perennial (`ownBroadcastChan_nonblocking_receive`'s proof, at fixed
names).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A non-blocking receive at the internal names `γi`**: not ready while the channel is open
(never once its done flag is known, `cl = .Done`), or it returns once the channel is closed, with
the flag. -/
theorem bcastInternal_nb_recv (ch : GoChan) (γ : ChanNames) (γi : BroadcastInternalNames)
    (Q : IProp GF) (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) (cl : Broadcast) :
    ⊢ isBroadcastChanInternal ch γ γi Q -∗
      (match cl with
       | .Done => dghostVar γi.doneGn .discard true
       | _ => iprop(True)) -∗
      ((dghostVar γi.doneGn .discard true -∗ Φ () false) ∧
        (match cl with
         | .Done => iprop(True)
         | _ => Φnotready)) -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro #Hint Hcl HΦ
  ihave #Hinv := isBroadcastChanInternal_inv _ _ _ _ $$ Hint
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .Idle; dsimp only; iframe
      imodintro
      iexact HΦ
  case RcvPending =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hcl Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .RcvPending; dsimp only; iframe
      imodintro
      iexact HΦ
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    icases HΦ with ⟨HΦ, -⟩
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iapply HΦ $$ Hs
  all_goals (iexfalso; iexact Hs)

/-- **A non-blocking `select` on the channel at its internal names** (`select { case <-ch: ...;
default: ... }`): its case runs once the channel is closed, with the done flag, or its default
(never once the flag is known, `cl = .Done`). -/
theorem wp_select_internal (ch : GoChan) (γ : ChanNames) (γi : BroadcastInternalNames)
    (Q : IProp GF) (cl : Broadcast) (handler dflt : Expr) (Φ : val → IProp GF) :
    ⊢ isBroadcastChanInternal ch γ γi Q -∗
      (match cl with
       | .Done => dghostVar γi.doneGn .discard true
       | _ => iprop(True)) -∗
      ((dghostVar γi.doneGn .discard true -∗ WP (App handler (Val (PairV #() #false))) {{ Φ }}) ∧
        (match cl with
         | .Done => iprop(True)
         | _ => WP dflt {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt)
        [CommClause (RecvCase (go.StructType []) (Val #ch)) handler]))) {{ Φ }} := by
  rcases cl with _ | _ | _
  all_goals dsimp only
  case Done =>
    iintro #Hint Hcl Hh
    iapply chan.wp_select_nonblocking_alt [iprop(False)] _ $$ [Hcl] Hh
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro Hh
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isBroadcastChanInternal_is_chan $$ Hint
      iapply bcastInternal_nb_recv ch γ γi Q _ _ .Done $$ Hint Hcl
      isplit
      · iintro #Hd
        icases Hh with ⟨Hh, -⟩
        iapply Hh $$ Hd
      · itrivial
    · iintro - Hnr
      iexfalso
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ (P : IProp GF) => P)).1 $$ Hnr
  all_goals
    iintro #Hint - Hh
    iapply chan.wp_select_nonblocking_alt [iprop(True)] _ $$ [] Hh
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro Hh
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isBroadcastChanInternal_is_chan $$ Hint
      iapply bcastInternal_nb_recv ch γ γi Q _ _ .Unknown $$ Hint []
      · itrivial
      isplit
      · iintro #Hd
        icases Hh with ⟨Hh, -⟩
        iapply Hh $$ Hd
      · dsimp only
        isplitl [Hh]
        · iexact Hh
        · itrivial
    · iintro Hh -
      icases Hh with ⟨-, Hh⟩
      iexact Hh

end proof

end EtcdGrove
end Perennial
