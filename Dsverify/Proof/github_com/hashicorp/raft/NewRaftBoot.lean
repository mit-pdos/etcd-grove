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

/-- (hraft_robust R5) The pure facts of the crash state (`durCore`'s). -/
def durPure (X : SrvDur) : Prop :=
  logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
    uint.nat X.A.ci ≤ X.s.dur.1 ∧ (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
    (∀ x st id, X.pend = some (x, st, id) → ∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
    (∀ d, X.dp = some d → X.c < d.x))

theorem durCore_pure (X : SrvDur) : durCore γ rc i X ⊢ durCore γ rc i X ∗ ⌜durPure X⌝ := by
  unfold durCore
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp, H10⟩
  iframe
  ipureintro; exact ⟨Hp, Hp⟩

theorem boot_dur_storeN : (↑durN : CoPset) ⊆ ⊤ \ ↑storeN := by
  unfold durN raftN storeN; solve_ndisj

/-- (hraft_robust R5) **A log-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_L (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (K : LogAbs → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ durPure X⌝ -∗ K X.A) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownL a ∗ (rc.ownL a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hld⟩
  iexists _
  iframe HL
  iintro HL
  imod Hmask with -
  imod Hcl $$ Hc [HL HS HSS Hld] with Hv
  · iunfold durStores; iframe
  obtain ⟨hA, hlat⟩ := HX
  subst hA hlat
  imodintro
  iapply HK $$ Hv Hsv
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hp⟩

/-- (hraft_robust R5) **A stable-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_S (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (K : StableAbs → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ durPure X⌝ -∗ K X.D) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownS a ∗ (rc.ownS a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hld⟩
  iexists _
  iframe HS
  iintro HS
  imod Hmask with -
  imod Hcl $$ Hc [HL HS HSS Hld] with Hv
  · iunfold durStores; iframe
  obtain ⟨hA, hlat⟩ := HX
  subst hA hlat
  imodintro
  iapply HK $$ Hv Hsv
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hp⟩

/-- (hraft_robust R5) **A snapshot-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_SS (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (K : SnapLatest → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ durPure X⌝ -∗ K X.lat) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownSS a ∗ (rc.ownSS a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hld⟩
  iexists _
  iframe HSS
  iintro HSS
  imod Hmask with -
  imod Hcl $$ Hc [HL HS HSS Hld] with Hv
  · iunfold durStores; iframe
  obtain ⟨hA, hlat⟩ := HX
  subst hA hlat
  imodintro
  iapply HK $$ Hv Hsv
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hp⟩

end boot

end github_com.hashicorp.raft

end Perennial
