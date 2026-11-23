/-
The connection reader's lock (`ConnReader.lean`): `lock` (the mutex, then the condition variable made
once) and `unlock`, for the proofs of its methods.
-/
module

public import Net.Proof.net.http.ConnReader
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- `sync.NewCond(m)` with its result not `nil` (Perennial's `NewCond.spec` does not say so:
`notes/perennial-changes.md`, 2026-11-23): its proof, over the translated body, with the
allocation's location kept. -/
theorem wp_NewCond_nn (m : GoInterfaceOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! sync.NewCond)) (Val #(interface.ok m)))
    {{ (c : Loc), RET #c; ⌜c ≠ null⌝ ∗ sync.isCond c m }} := by
  wp_start as _
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  ipersist L
  ipersist notify
  imod inv_alloc sync.copyCheckerN ⊤ (sync.copyCheckerInv _) $$ [checker] with #Hchecker
  · inext; ileft; iexact checker
  imodintro
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  rw [sync.isCond_unseal]; unfold sync.isCondDef
  rw [sync.isCopyChecker_unseal]; unfold sync.isCopyCheckerDef
  iframe #
  done

/-- `cr.lock()`: the mutex held, the condition variable made. -/
theorem wp_cr_lock (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8)
    (Z : Nat → IProp GF) :
    {{ crIs cr γ cn P hs Z }}
      (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"lock")) (Val #()))
    {{ RET #(); sync.ownMutex (structFieldRef net.http.connReader go!"mu" cr) ∗
        (∃ cv, crCond cr cv) ∗ crPh cr γ cn P hs Z }} := by
  wp_start as #Hcr
  iapply wp_fupd
  iunfold crIs at Hcr
  icases Hcr with ⟨#Hsync, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold crInv at Hinv
  icases Hinv with ⟨(Hc | ⟨%cv, #Hc⟩), Hph⟩
  · wp_auto
    wp_apply wp_NewCond_nn as %cv ⟨%Hcv, #Hcond⟩
    ipersist Hc
    imodintro
    iapply HΦ
    iframe Hown Hph
    iexists cv
    iunfold crCond
    iframe Hc Hcond
    ipureintro; exact Hcv
  · iunfold crCond at Hc
    icases Hc with ⟨%Hcv, #Hc, #Hcond⟩
    wp_auto
    simp only [Hcv, decide_false]
    wp_auto
    imodintro
    iapply HΦ
    iframe Hown Hph
    iexists cv
    iunfold crCond
    iframe Hc Hcond
    ipureintro; exact Hcv

/-- `cr.unlock()`. -/
theorem wp_cr_unlock (cr : Loc) (γ : CrNames) (cn : Nat) (P : Proto GF) (hs : List w8)
    (Z : Nat → IProp GF) (cv : Loc) :
    {{ crIs cr γ cn P hs Z ∗ sync.ownMutex (structFieldRef net.http.connReader go!"mu" cr) ∗
        crCond cr cv ∗ ▷ crPh cr γ cn P hs Z }}
      (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"unlock")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hcr, Hown, #Hc, Hph⟩
  iunfold crIs at Hcr
  icases Hcr with ⟨#Hsync, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hph]
  · inext
    iunfold crInv
    iframe Hph
    iright; iexists cv; iexact Hc
  iapply HΦ; itrivial

/-- `w.closeNotify()` on a response whose close notification has no channel. -/
theorem wp_closeNotify (w : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ respNotify w }}
      (App (Val (w @!! go.GoType.PointerType net.http.response.ty @!! go!"closeNotify")) (Val #()))
    {{ RET #(); True }} := by
  unfold respNotify
  wp_start as #Hn
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hn] as ⟨Hown, %t, Ht, Hch⟩
  cases t
  · wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hn $Hown Ht Hch]
    · inext; iexists true; iframe
    iapply HΦ; itrivial
  · wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hn $Hown Ht Hch]
    · inext; iexists true; iframe
    iapply HΦ; itrivial

/-- `cr.handleReadErrorLocked(err)`: the connection's context canceled and its current response
notified, if the reader still has its connection. -/
theorem wp_handleReadErrorLocked (cr c : Loc) (err : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
        structFieldRef net.http.connReader go!"conn" cr ↦ c ∗ crConnOk c }}
      (App (Val (cr @!! go.GoType.PointerType net.http.connReader.ty @!! go!"handleReadErrorLocked"))
        (Val #err))
    {{ RET #(); structFieldRef net.http.connReader go!"conn" cr ↦ c }} := by
  wp_start as ⟨Hc, #Hok⟩
  iunfold crConnOk at Hok
  icases Hok with (%Hnull | ⟨%f, %γc, %Hnn, #Hf, #Hcancel, #Hinv⟩)
  · subst Hnull
    wp_auto
    iapply HΦ $$ Hc
  · wp_auto
    simp only [Hnn, decide_false]
    wp_auto
    iunfold context.cancelSpec at Hcancel
    wp_bind (App (Val #f) (Val #()))
    iapply Hcancel
    · imodintro; itrivial
    inext
    iintro -
    wp_auto
    wp_bind (App (Val #(methods _ _ _)) (Val #()))
    iapply (sync.atomic.Pointer.wp_Load (T' := net.http.response) net.http.response.ty
      (structFieldRef net.http.conn go!"curReq" c) (DFrac.own 1))
    · iPkgInit
    unfold curReqInv
    iinv Hinv with ⟨%v, >Hv, #Hr⟩ Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists v
    iframe Hv
    iintro Hv
    imod Hmask
    imod Hclose $$ [Hv] with -
    · inext; iexists v; iframe Hv Hr
    imodintro
    wp_auto
    icases Hr with (%Hvn | ⟨%Hvn, #Hr⟩)
    · subst Hvn
      wp_auto
      iapply HΦ $$ Hc
    · simp only [Hvn, decide_false]
      wp_auto
      wp_apply wp_closeNotify $$ [$Hr]
      iapply HΦ $$ Hc


end lemmas

end net.http
end Perennial
