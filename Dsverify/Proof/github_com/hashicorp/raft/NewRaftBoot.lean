/-
(hraft_robust R5) **The crash invariant during `NewRaft`** (the boot): opening the raw invariant with the
boot pin's other half, which fixes the stores' state the restore reads (`X.A`, `X.lat`), and ending the boot
(the pin discarded at `none`: `bootOver`, so that `srvDurInv` holds). A defs module of `NewRaft`'s proof.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

variable (γ : GNames) (rc : RCtx GF) (i : SID)

/-- `NewRaft`'s half of the boot pin. -/
def bootV (A : LogAbs) (lat : SnapLatest) : IProp GF :=
  dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) (some (A, lat))

instance bootV_timeless A lat : Timeless (bootV (GF := GF) rc A lat) := by
  unfold bootV; infer_instance

instance bootPin_timeless' X : Timeless (bootPin (GF := GF) rc X) := by
  unfold bootPin; infer_instance

/-- The boot pin of the crash state agrees with `NewRaft`'s half. -/
theorem bootPin_agree (X : SrvDur) (A : LogAbs) (lat : SnapLatest) :
    bootPin rc X ∗ bootV rc A lat ⊢
      dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) (some (A, lat)) ∗ bootV rc A lat ∗
        ⌜X.A = A ∧ X.lat = lat⌝ := by
  unfold bootPin bootV
  iintro ⟨(⟨%o, Ho, %Hp⟩ | Hd), Hv⟩
  · icombine Ho Hv gives %Hag
    obtain ⟨-, rfl⟩ := Hag
    obtain h := Hp (A, lat) rfl
    simp only [Prod.mk.injEq] at h
    iframe
    ipureintro; exact ⟨h.1.symm, h.2.symm⟩
  · icombine Hd Hv gives %Hag
    cases Hag.2

/-- (hraft_robust R5) **Opening the raw crash invariant during the boot**: the crash state, with its stores'
state the pinned one, its core without its later; the closing re-pins at the new state's stores. -/
theorem bootOpen {E : CoPset} (hE : ↑durN ⊆ E) (A : LogAbs) (lat : SnapLatest) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ⊢ |NC={E, E \ ↑durN}=> ∃ X : SrvDur,
      ⌜X.A = A ∧ X.lat = lat⌝ ∗ durCore γ rc i X ∗ ▷ durStores γ rc i X ∗
      (∀ X' : SrvDur, durCore γ rc i X' -∗ ▷ durStores γ rc i X' ={E \ ↑durN, E}=∗ bootV rc X'.A X'.lat) := by
  iintro ⟨#Hi, Hv⟩ Hnc
  unfold srvDurInvRaw
  imod (inv_nc_acc hE) $$ Hi Hnc with ⟨Hnc, HX, Hcl⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  ihave HX := later_mono (durBody_split γ rc i X).1 $$ HX
  icases HX with ⟨>Hc, Hs, >Hb⟩
  ihave ⟨Hb, Hv, %Hag⟩ := bootPin_agree rc X A lat $$ [Hb Hv]
  · iframe
  imodintro
  iframe Hnc
  iexists X
  iframe Hc Hs
  isplitr
  · ipureintro; exact Hag
  iintro %X' Hc' Hs'
  unfold bootV
  imod dghostVar_update_halves (some (X'.A, X'.lat)) _ _ _ $$ Hb Hv with ⟨Hb, Hv⟩
  imod Hcl $$ [Hc' Hs' Hb] with -
  · inext
    iexists X'
    iapply (durBody_split γ rc i X').2
    iframe
    unfold bootPin
    ileft
    iexists _
    iframe
    ipureintro; intro p hp; cases hp; rfl
  imodintro
  iexact Hv

/-- (hraft_robust R5) **Ending the boot**: the pin discarded at `none` (`bootOver`), `srvDurInv` from the raw
invariant. -/
theorem bootEnd {E : CoPset} (hE : ↑durN ⊆ E) (A : LogAbs) (lat : SnapLatest) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ⊢ |NC={E}=> srvDurInv γ rc i := by
  iintro ⟨#Hi, Hv⟩ Hnc
  ihave Hi' := Hi
  unfold srvDurInvRaw
  imod (inv_nc_acc hE) $$ Hi' Hnc with ⟨Hnc, HX, Hcl⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  ihave HX := later_mono (durBody_split γ rc i X).1 $$ HX
  icases HX with ⟨Hc, Hs, >Hb⟩
  ihave ⟨Hb, Hv, -⟩ := bootPin_agree rc X A lat $$ [Hb Hv]
  · iframe
  unfold bootV
  icombine Hb Hv as Hb
  imod dghostVar_update (none : Option (LogAbs × SnapLatest)) _ _ $$ Hb with Hb
  imod dghostVar_persist _ _ _ $$ Hb with #Hb
  imod Hcl $$ [Hc Hs] with -
  · inext
    iexists X
    iapply (durBody_split γ rc i X).2
    iframe
    unfold bootPin
    iright
    iexact Hb
  imodintro
  iframe Hnc
  unfold srvDurInv bootOver srvDurInvRaw
  iframe #

end boot

end github_com.hashicorp.raft

end Perennial
