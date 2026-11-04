/-
Lean-first (no Rocq counterpart).

# A bag channel's non-blocking send (kvreconf-snapshot-thread, 2026-10-30)

Perennial's bag idiom (`Chan/Idioms/Bag.lean`) has the blocking send's atomic update
(`bag_send_au`), not the non-blocking one a `select` with a `default` needs: here it is, generic
(`notes/perennial-changes.md`: a candidate for the idiom). A send that completes (a buffered slot,
or a waiting receiver) hands `P v` to the invariant; one that cannot completes nothing, and the
caller keeps `P v` in the `default` branch (`nonblockingSendAu`'s `∧`).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- **A bag channel's non-blocking send**: the atomic update of a send that completes. -/
theorem bag_nb_send_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ P v -∗ ▷ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro Hlc1 ⟨#Hch, #Hinv⟩ HP HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

end proof

end EtcdGrove
end Perennial
