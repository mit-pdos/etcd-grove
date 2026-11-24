/-
A variant of Perennial's SPSC receive (`Perennial/Golang/Theory/Chan/Idioms/Spsc.lean`, `spsc_rcv_au`,
`wp_spsc_receive`) for a persistent final resource `R`: on the closed and drained channel the consumer
learns `R received` and KEEPS its token `spscConsumer γ received` (Perennial's swaps the token into the
invariant for `R`, so a second receive is impossible to prove). Needed by prometheus's
`(*Registry).Register`, whose deferred `for range descChan {}` receives again after the main loop has
seen the close (notes/prom-registry.md, route (b), step 2). A copy of Perennial's proof with the
`Closed []` case changed; a candidate Perennial addition (notes/perennial-changes.md).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spsc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]


omit [IntoValTyped (GF := GF) V t] in
set_option maxHeartbeats 400000 in
theorem spsc_rcv_au_peek (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF) (R : List V → IProp GF) [HR : ∀ l, Persistent (R l)]
    (received : List V) (Φ : V → Bool → IProp GF) :
    ⊢ isSpsc γ ch P R -∗ £ 1 ∗ £ 1 -∗ spscConsumer γ received -∗
      ▷ (∀ (v : V) (ok : Bool),
          (if ok then iprop(P received.length v ∗ spscConsumer γ (received ++ [v]))
           else iprop(R received ∗ spscConsumer γ received ∗ ⌜v = zero_val V⌝)) -∗ Φ v ok) -∗
      recvAu γ.chanName V Φ := by
  unfold isSpsc recvAu
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ Hcons Hcont
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spscConsumer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered b =>
    cases b with
    | nil => itrivial
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      icases (spsc_pop P received v rest).1 $$ Hm with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest] with -
      · inext
        iapply spscInv_intro γ P R (.Buffered rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        iexact Hrest
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
  | Idle =>
    dsimp only
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply spscInv_intro γ P R .RcvPending sent received (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      itrivial
    imodintro
    unfold recvNestedAu
    iapply ncfupd_of_fupd
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
    ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hcons HrecvI
    subst Heq
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    cases s with
    | SndCommit v =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI] with -
      · inext
        iapply spscInv_intro γ P R .Idle sent (received ++ [v]) (by simpa [inflight] using Hrel)
          $$ Hoc HsentI HrecvI
        simp only [spscInvMatch]
        itrivial
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
    | Closed d =>
      cases d with
      | nil =>
        dsimp only
        simp only [inflight, List.append_nil] at Hrel
        subst Hrel
        simp only [spscInvMatch, spscConsumer]
        icases Hm with ⟨Hprod, (#HR | Hc2)⟩
        · iintro Hoc
          imod Hmask with -
          imod Hclose $$ [Hoc HsentI HrecvI Hprod] with -
          · inext
            iapply spscInv_intro γ P R (.Closed []) sent sent (by simp [inflight])
              $$ Hoc HsentI HrecvI
            simp only [spscInvMatch, spscConsumer]
            isplitl [Hprod]
            · iexact Hprod
            · ileft; iexact HR
          imodintro
          iapply Hcont
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          iexact HR
        · iexfalso
          iapply dghostVar_three_halves $$ Hcons HrecvI Hc2
      | cons _ _ => itrivial
    | _ => itrivial
  | SndPending v =>
    dsimp only
    iintro Hoc
    imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
    simp only [spscInvMatch]
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI] with -
    · inext
      iapply spscInv_intro γ P R .RcvCommit sent (received ++ [v]) (by simpa [inflight] using Hrel)
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      itrivial
    imodintro
    iapply Hcont
    simp only [↓reduceIte]
    iframe
  | Closed d =>
    cases d with
    | nil =>
      dsimp only
      simp only [inflight, List.append_nil] at Hrel
      subst Hrel
      simp only [spscInvMatch, spscConsumer]
      icases Hm with ⟨Hprod, (#HR | Hc2)⟩
      · iintro Hoc
        imod Hmask with -
        imod Hclose $$ [Hoc HsentI HrecvI Hprod] with -
        · inext
          iapply spscInv_intro γ P R (.Closed []) sent sent (by simp [inflight])
            $$ Hoc HsentI HrecvI
          simp only [spscInvMatch, spscConsumer]
          isplitl [Hprod]
          · iexact Hprod
          · ileft; iexact HR
        imodintro
        iapply Hcont
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        iexact HR
      · iexfalso
        iapply dghostVar_three_halves $$ Hcons HrecvI Hc2
    | cons v rest =>
      dsimp only
      iintro Hoc
      imod dghostVar_update_halves (received ++ [v]) _ _ _ $$ Hcons HrecvI with ⟨Hcons, HrecvI⟩
      simp only [spscInvMatch]
      icases Hm with ⟨Hbig, Hprod, Hor⟩
      icases (spsc_pop P received v rest).1 $$ Hbig with ⟨HPv, Hrest⟩
      imod Hmask with -
      imod Hclose $$ [Hoc HsentI HrecvI Hrest Hprod Hor] with -
      · inext
        iapply spscInv_intro γ P R (.Closed rest) sent (received ++ [v]) (by simp [Hrel, inflight])
          $$ Hoc HsentI HrecvI
        cases rest with
        | nil =>
          simp only [spscInvMatch]
          isplitl [Hprod]
          · iexact Hprod
          · iexact Hor
        | cons w ws =>
          simp only [spscInvMatch]
          isplitl [Hrest]
          · iexact Hrest
          isplitl [Hprod]
          · iexact Hprod
          · iexact Hor
      imodintro
      iapply Hcont
      simp only [↓reduceIte]
      iframe
  | _ => itrivial

/-- SPSC receive, keeping the consumer token on the closed and drained channel (`R` persistent). -/
theorem wp_spsc_receive_peek (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) [HR : ∀ l, Persistent (R l)] (received : List V) :
    {{ isSpsc γ ch P R ∗ spscConsumer γ received }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(P received.length v ∗ spscConsumer γ (received ++ [v]))
         else iprop(R received ∗ spscConsumer γ received ∗ ⌜v = zero_val V⌝)) }} := by
  iintro %Φ ⟨#Hspsc, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.chanName V $$ [Hspsc]
  · unfold isSpsc; icases Hspsc with ⟨$, -⟩
  iapply chan.wp_receive ch γ.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply spsc_rcv_au_peek γ ch P R received (fun v ok => Φ (PairV #v #ok)) $$ Hspsc [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

end spsc

end EtcdGrove
end Perennial
