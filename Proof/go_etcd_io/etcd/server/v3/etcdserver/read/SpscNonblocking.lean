/-
A nonblocking send on a single-producer single-consumer channel (Perennial's `isSpsc`,
`Perennial/Golang/Theory/Chan/Idioms/Spsc.lean`): `spsc_nonblocking_send_au`, the producer's
`nonblockingSendAuInner` for a `select { case ch <- v: ...; default: ... }`. Perennial's SPSC idiom
has the blocking send only (`spsc_send_au`); this is its nonblocking twin, proved here from the idiom's
exported lemmas the same way (an idle channel is the "not ready" case, which commits nothing). Local
to this repository (CLAUDE.md, "Changes to Perennial"): it belongs in `Spsc.lean`, as a general
Perennial change of its own. Written for etcd PR #22242 (2026-10-17), whose read loop hands its trace to
the logger goroutine with a nonblocking send.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spsc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option maxHeartbeats 400000 in
/-- The producer's nonblocking send of `v` with `P sent.length v`: if the channel takes `v` (a
receiver waiting, or room in the buffer), the producer's history grows by `v` (`Φ`); the channel is
never closed while the producer holds its token. -/
theorem spsc_nonblocking_send_au (γ : SpscNames) (ch : Loc) (P : Int → V → IProp GF)
    (R : List V → IProp GF) (sent : List V) (v : V) (Φ : IProp GF) :
    ⊢ isSpsc γ ch P R -∗ £ 1 ∗ £ 1 -∗ spscProducer γ sent ∗ P sent.length v -∗
      ▷ (spscProducer γ (sent ++ [v]) -∗ Φ) -∗ nonblockingSendAuInner γ.chanName v Φ := by
  unfold isSpsc nonblockingSendAuInner
  iintro ⟨#Hchan, #Hinv⟩ ⟨Hlc1, Hlc2⟩ ⟨Hprod, HP⟩ Hcont
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 Hcont with Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
  icases spscInv_elim _ _ _ $$ Hi with ⟨%s, %sent0, %recv, Hch, HsentI, HrecvI, %Hrel, Hm⟩
  unfold spscProducer
  ihave %Heq := dghostVar_agree _ _ _ _ _ $$ Hprod HsentI
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  cases s with
  | Buffered buff =>
    dsimp only
    simp only [inflight] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves ((recv ++ buff) ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI Hm HP] with -
    · inext
      iapply spscInv_intro γ P R (.Buffered (buff ++ [v])) ((recv ++ buff) ++ [v]) recv
        (by simp [inflight]) $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      iapply spsc_push P recv buff v
      isplitl [Hm]
      · iexact Hm
      · iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | RcvPending =>
    dsimp only
    simp only [inflight, List.append_nil] at Hrel
    subst Hrel
    iintro Hoc
    imod dghostVar_update_halves (sent ++ [v]) _ _ _ $$ Hprod HsentI with ⟨Hprod, HsentI⟩
    imod Hmask with -
    imod Hclose $$ [Hoc HsentI HrecvI HP] with -
    · inext
      iapply spscInv_intro γ P R (.SndCommit v) (sent ++ [v]) sent (by simp [inflight])
        $$ Hoc HsentI HrecvI
      simp only [spscInvMatch]
      iexact HP
    imodintro
    iapply Hcont $$ Hprod
  | Closed d =>
    dsimp only
    cases d with
    | nil =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
    | cons _ _ =>
      simp only [spscInvMatch, spscProducer]
      icases Hm with ⟨-, Hp2, -⟩
      iapply dghostVar_three_halves $$ Hprod HsentI Hp2
  | _ => itrivial

end spsc

end EtcdGrove
end Perennial
