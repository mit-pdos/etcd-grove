/-
The proof of `Call.done` (`Net/Spec/net/rpc/Call__done.lean`): the `select`'s send case fulfils the
future (`future_fulfill_nb`: the future idiom's fulfilment as a non-blocking send's update, the
`Buffered` and `RcvPending` cases of `future_fulfill_au`; a full buffer or no waiting receiver
is not ready); its `default` case reads `debugLog` (`false`) and does nothing.
-/
module

public import Net.Spec.net.rpc.Call__done

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- The future idiom's fulfilment by a non-blocking send (a `select` case with a `default`): when
the send happens, the value goes to the future with its contract. (A general fact of Perennial's
`Chan/Idioms/Future.lean`, proved here: `notes/perennial-changes.md`.) -/
theorem future_fulfill_nb {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (γ : FutureNames) (ch : Loc) (v : V) (Φ : IProp GF) :
    ⊢ isFuture V γ ch -∗ £ 1 -∗ Fulfilled γ v -∗ ▷ Φ -∗
      nonblockingSendAuInner γ.chanName v Φ := by
  unfold isFuture nonblockingSendAuInner
  iintro ⟨#Hisch, #Hinv⟩ Hlc1 HFulfilled HΦ
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold futureInv
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
    imod Hclose $$ [Hoc Hi HFulfilled] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HFulfilled
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HFulfilled] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals itrivial

theorem Call.done.wp_proof : Call.done.spec (GF := GF) (hG := hG) := by
  intro pc sm args reply ch γ γt γf K Φ Θ D o err
  unfold callDone
  wp_start as ⟨#Hdbg, #Hf, #Ht, ⟨#Hfut, Hful, HK⟩, Herr, Hpost⟩
  unfold callFields
  ihave HK' := HK $$ %pc %o %err Hf Ht Herr Hpost
  icases Hf with ⟨#Hsm, #Hargs, #Hrep, #Hch⟩
  wp_auto_lc 1
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γf.chanName, pc
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · unfold isFuture; icases Hfut with ⟨$, -⟩
      unfold nonblockingSendAu
      isplit
      · iapply future_fulfill_nb γf ch pc $$ Hfut Hlc1 [Hful HK']
        · unfold Fulfilled; iexists K; iframe Hful HK'
        inext
        wp_auto
        iapply HΦ
        itrivial
      · itrivial
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end net.rpc
end Perennial
