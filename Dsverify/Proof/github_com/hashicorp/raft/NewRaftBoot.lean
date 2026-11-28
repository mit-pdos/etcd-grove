/-
(hraft_robust R5) **The crash invariant during `NewRaft`** (the boot): opening the raw invariant with the
boot pin's other half, which fixes the stores' state the restore reads (`X.A`, `X.lat`), and ending the boot
(the pin discarded at `none`: `bootOver`, so that `srvDurInv` holds). A defs module of `NewRaft`'s proof.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftRec
public import Perennial.Proof.sync.atomic.Link
public import Dsverify.Proof.github_com.hashicorp.raft.core.LastLock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section atomicNc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- `sync.atomic.StoreUint64` with a crash-token atomic update (a copy of R4a's `DurHelpers` lemma, whose module
imports `core/CrashLaws`). -/
theorem boot_wp_StoreUint64_nc (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|NC={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! sync.atomic.StoreUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (SwapBytes _ _ _)
  iapply wp_atomic_nc _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HΦ⟩
  iframe Hnc
  imodintro
  icases HΦ with ⟨%oldv, Haddr, HΦ⟩
  wp_apply_core wp_swap_bytes_typed _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

end atomicNc

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

variable (γ : GNames) (rc : RCtx GF) (i : SID)


/-- (hraft_robust R5) **`durCore` during the boot**: without its boot-over part (`bootPinF`), which the
boot pin replaces until `NewRaft` ends the boot. -/
def durCoreB (X : SrvDur) : IProp GF :=
  iprop(srvOwn γ i X.s ∗ durView γ i (1 : Qp).half X.s.dur.1 ∗ logCouple γ i X.s.log ∗
    termCouple γ i X.s.term ∗ cidxCouple γ i X.s.cidx ∗
    ghostVar rc.dur.sv (1 : Qp).half (X.s, X.tp, X.dp) ∗ ghostVar rc.dur.st (1 : Qp).half (X.D, X.A.staged) ∗
    ghostVar rc.dur.tv (1 : Qp).half X.s.term ∗ ghostVar rc.dur.cv (1 : Qp).half X.s.cidx ∗
    ⌜logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
      uint.nat X.A.ci ≤ X.s.dur.1 ∧ (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
      (∀ x st id, X.pend = some (x, st, id) → (∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∨
        (prevMatch X.s.log x st ∧ x ≤ X.s.dur.1)) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
      ((∀ d, X.dp = some d → X.c < d.x) ∧ ((X.tp = none ∨ X.dp = none) ∧
        (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st))))⌝ ∗
    monoNatAuthOwn rc.dur.comp (1 : Qp).half X.c ∗ ghostVar rc.dur.pend (1 : Qp).half X.pend ∗
    tpRes γ X.tp ∗ dpRes γ i X.s X.dp ∗ monoNatAuthOwn rc.dur.lat 1 (latIdxD X.lat))

instance durCoreB_timeless (X : SrvDur) : Timeless (durCoreB γ rc i X) := by
  unfold durCoreB; infer_instance

theorem durCore_B (X : SrvDur) :
    durCore γ rc i X ⊣⊢ durCoreB γ rc i X ∗ bootPinF rc X.lat X.pend X.dp := by
  unfold durCore durCoreB
  refine ⟨?_, ?_⟩
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hp, H10, H11, H12, H13, H14, H15⟩
    iframe
  · iintro ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hp, H10, H11, H12, H13, H14⟩, H15⟩
    iframe

/-- (hraft_robust R5) `durBody` during the boot: its core without the boot-over part, its stores and the pin. -/
theorem durBody_splitB (X : SrvDur) :
    durBody γ rc i X ⊣⊢ durCoreB γ rc i X ∗ durStores γ rc i X ∗ bootPin rc X := by
  unfold durBody durCoreB durStores
  refine ⟨?_, ?_⟩
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, HL, HS, HSS, %Hp, %Hq, Hb, Hc, %Hr, %Hs5, Hla, Hl, Hpe, Ht, Hd⟩
    iframe
    ipureintro; exact ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.1, Hp.2.2.2.2, Hq, Hr, Hs5⟩
  · iintro ⟨⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp, Hc, Hpe, Ht, Hd, Hla⟩, ⟨HL, HS, HSS, Hl⟩, Hb⟩
    iframe
    isplitl []
    · ipureintro; exact ⟨Hp.1, Hp.2.1, Hp.2.2.1, Hp.2.2.2.1, Hp.2.2.2.2.1⟩
    isplitl []
    · ipureintro; exact Hp.2.2.2.2.2.1
    iframe
    ipureintro; exact Hp.2.2.2.2.2.2

theorem durCoreB_srvVP_agree (X : SrvDur) (s : SState) (tp : Option TermPend) (dp : Option DiscPend) :
    durCoreB γ rc i X ∗ srvVP rc s tp dp ⊢
      durCoreB γ rc i X ∗ srvVP rc s tp dp ∗ ⌜X.s = s ∧ X.tp = tp ∧ X.dp = dp⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCoreB srvVP
  icases Hc with ⟨H1, H2, H3, H4, H5, Hsv, H7⟩
  icombine Hsv Hv gives %H
  have H := H.2
  simp only [Prod.mk.injEq] at H
  iframe
  ipureintro; exact H

theorem durCoreB_stVS_agree (X : SrvDur) (D : StableAbs) (g : w64) :
    durCoreB γ rc i X ∗ stVS rc D g ⊢ durCoreB γ rc i X ∗ stVS rc D g ∗ ⌜X.D = D ∧ X.A.staged = g⌝ := by
  iintro ⟨Hc, Hv⟩
  unfold durCoreB stVS
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, Hst, H8⟩
  icombine Hst Hv gives %H
  have H := H.2
  simp only [Prod.mk.injEq] at H
  iframe
  ipureintro; exact H

/-- `NewRaft`'s half of the boot pin. -/
def bootV (A : LogAbs) (lat : SnapLatest) : IProp GF :=
  dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) (some (A, lat))

instance bootV_timeless A lat : Timeless (bootV (GF := GF) rc A lat) := by
  unfold bootV; infer_instance

instance latApplOk_timeless' X : Timeless (latApplOk (GF := GF) rc X) := by
  unfold latApplOk applLb; rcases X.lat with _ | ⟨_, _⟩ <;> infer_instance

instance bootPin_timeless' X : Timeless (bootPin (GF := GF) rc X) := by
  unfold bootPin; infer_instance

/-- The boot pin of the crash state agrees with `NewRaft`'s half. -/
theorem bootPin_agree (X : SrvDur) (A : LogAbs) (lat : SnapLatest) :
    bootPin rc X ∗ bootV rc A lat ⊢
      dghostVar rc.dur.boot (DFrac.own (1 : Qp).half) (some (A, lat)) ∗ bootV rc A lat ∗
        ⌜X.A = A ∧ X.lat = lat⌝ := by
  unfold bootPin bootV
  iintro ⟨(Ho | ⟨Hd, -⟩), Hv⟩
  · icombine Ho Hv gives %Hag
    obtain ⟨-, h⟩ := Hag
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    iframe
    ipureintro; exact ⟨h1, h2⟩
  · icombine Hd Hv gives %Hag
    cases Hag.2

/-- (hraft_robust R5) **Opening the raw crash invariant during the boot**: the crash state, with its stores'
state the pinned one, its core without its later; the closing re-pins at the new state's stores. -/
theorem bootOpen {E : CoPset} (hE : ↑durN ⊆ E) (A : LogAbs) (lat : SnapLatest) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ⊢ |NC={E, E \ ↑durN}=> ∃ X : SrvDur,
      ⌜X.A = A ∧ X.lat = lat⌝ ∗ durCoreB γ rc i X ∗ ▷ durStores γ rc i X ∗
      (∀ X' : SrvDur, durCoreB γ rc i X' -∗ ▷ durStores γ rc i X' ={E \ ↑durN, E}=∗ bootV rc X'.A X'.lat) := by
  iintro ⟨#Hi, Hv⟩ Hnc
  unfold srvDurInvRaw
  imod (inv_nc_acc hE) $$ Hi Hnc with ⟨Hnc, HX, Hcl⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  ihave HX := later_mono (durBody_splitB γ rc i X).1 $$ HX
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
    iapply (durBody_splitB γ rc i X').2
    iframe
    unfold bootPin
    ileft
    iexact Hb
  imodintro
  iexact Hv

/-- (hraft_robust R5) **Ending the boot**: the pin discarded at `none` (`bootOver`), `srvDurInv` from the raw
invariant. -/
theorem bootEnd {E : CoPset} (hE : ↑durN ⊆ E) (A : LogAbs) (lat : SnapLatest) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗
      (match lat with | none => iprop(True) | some (m, _) => applLb rc (uint.nat m.Index')) ⊢
    |NC={E}=> srvDurInv γ rc i := by
  iintro ⟨#Hi, Hv, Hla⟩ Hnc
  ihave Hi' := Hi
  unfold srvDurInvRaw
  imod (inv_nc_acc hE) $$ Hi' Hnc with ⟨Hnc, HX, Hcl⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  ihave HX := later_mono (durBody_splitB γ rc i X).1 $$ HX
  icases HX with ⟨Hc, Hs, >Hb⟩
  ihave ⟨Hb, Hv, %Hag⟩ := bootPin_agree rc X A lat $$ [Hb Hv]
  · iframe
  unfold bootV
  icombine Hb Hv as Hb
  imod dghostVar_update (none : Option (LogAbs × SnapLatest)) _ _ $$ Hb with Hb
  imod dghostVar_persist _ _ _ $$ Hb with #Hb
  imod Hcl $$ [Hc Hs Hla] with -
  · inext
    iexists X
    iapply (durBody_splitB γ rc i X).2
    iframe
    unfold bootPin
    iright
    iframe #
    unfold latApplOk
    rw [Hag.2]
    rcases lat with _ | ⟨m, b⟩
    · itrivial
    · iright; iexact Hla
  imodintro
  iframe Hnc
  unfold srvDurInv bootOver srvDurInvRaw
  iframe #

/-- (hraft_robust R5) The pure facts of the crash state (`durCore`'s). -/
def durPure (X : SrvDur) : Prop :=
  logOk X.A X.s.log X.lo ∧ X.lo ≤ X.c + 1 ∧ voteMatches X.D X.s ∧ termDurOk X.D X.s X.tp ∧
    uint.nat X.A.ci ≤ X.s.dur.1 ∧ (((∀ d, X.dp = some d → X.lo ≤ d.x) ∧
    (∀ x st id, X.pend = some (x, st, id) → (∃ ℓ, X.dp = some ⟨x, st, ℓ⟩) ∨
      (prevMatch X.s.log x st ∧ x ≤ X.s.dur.1)) ∧ X.lo ≤ latIdxD X.lat + 1) ∧
    ((∀ d, X.dp = some d → X.c < d.x) ∧ ((X.tp = none ∨ X.dp = none) ∧
      (∀ d, X.dp = some d → ∃ m b, X.lat = some (m, b) ∧ uint.nat m.Index' = d.x ∧ uint.nat m.Term' = d.st))))

theorem durCoreB_pure (X : SrvDur) : durCoreB γ rc i X ⊢ durCoreB γ rc i X ∗ ⌜durPure X⌝ := by
  unfold durCoreB
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp, H10⟩
  iframe
  ipureintro; exact ⟨Hp, Hp⟩

theorem boot_dur_storeN : (↑durN : CoPset) ⊆ ⊤ \ ↑storeN := by
  unfold durN raftN storeN; solve_ndisj

/-- (hraft_robust R5) **A log-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_L (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (D : StableAbs) (g : w64) (K : LogAbs → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗ stVS rc D g ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ stVS rc D g -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ X.D = D ∧ X.A.staged = g ∧ durPure X⌝ -∗ K X.A) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownL a ∗ (rc.ownL a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, Hst, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCoreB_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  iapply HK $$ Hv Hsv Hst
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hag2.1, Hag2.2, Hp⟩

/-- (hraft_robust R5) **A stable-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_S (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (D : StableAbs) (g : w64) (K : StableAbs → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗ stVS rc D g ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ stVS rc D g -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ X.D = D ∧ X.A.staged = g ∧ durPure X⌝ -∗ K X.D) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownS a ∗ (rc.ownS a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, Hst, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCoreB_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  iapply HK $$ Hv Hsv Hst
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hag2.1, Hag2.2, Hp⟩

/-- (hraft_robust R5) **A snapshot-store read during the boot**: the store's atomic update, from the raw crash invariant
with the boot pin and the main goroutine's view; the continuation learns the crash state's facts. -/
theorem bootRead_SS (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend) (dp : Option DiscPend)
    (D : StableAbs) (g : w64) (K : SnapLatest → IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗ stVS rc D g ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ stVS rc D g -∗ ∀ X : SrvDur,
        ⌜X.A = A ∧ X.lat = lat ∧ X.s = s ∧ X.tp = tp ∧ X.dp = dp ∧ X.D = D ∧ X.A.staged = g ∧ durPure X⌝ -∗ K X.lat) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ a, rc.ownSS a ∗ (rc.ownSS a ={∅, ⊤ \ ↑storeN}=∗ K a) := by
  iintro ⟨#Hi, Hv, Hsv, Hst, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCoreB_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  iapply HK $$ Hv Hsv Hst
  ipureintro
  exact ⟨rfl, rfl, Hag.1, Hag.2.1, Hag.2.2, Hag2.1, Hag2.2, Hp⟩

theorem getD_insert_same {K V : Type} [DecidableEq K] [Pos.Countable K] (m : GMap K V) (kb k : K) (v d : V)
    (h : (m.lookup kb).getD d = v) : ((m.insert kb v).lookup k).getD d = (m.lookup k).getD d := by
  by_cases hk : kb = k
  · subst hk; rw [GMap.lookup_insert]; simpa using h.symm
  · rw [GMap.lookup_insert_ne _ _ hk]

/-- (hraft_robust R5) **An idempotent stable-store write during the boot** (`SetUint64(kb, v)` of the value
`kb` already reads as, `getD`): the store's atomic update, with the stable view updated; the crash state's
facts, which read the store through `getD`, are unchanged. -/
theorem bootRewrite_S (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend)
    (dp : Option DiscPend) (D : StableAbs) (g : w64) (kb : List w8) (v : w64)
    (h : (D.ints.lookup kb).getD (W64 0) = v) (K : IProp GF) :
    srvDurInvRaw γ rc i ∗ bootV rc A lat ∗ srvVP rc s tp dp ∗ stVS rc D g ∗
      (bootV rc A lat -∗ srvVP rc s tp dp -∗ stVS rc { D with ints := D.ints.insert kb v } g -∗ K) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ st, rc.ownS st ∗
      (rc.ownS { st with ints := st.ints.insert kb v } ={∅, ⊤ \ ↑storeN}=∗ K) := by
  iintro ⟨#Hi, Hv, Hsv, Hst, HK⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCoreB_stVS_agree γ rc i X D g $$ [Hc Hst]
  · iframe
  obtain ⟨hD, hg⟩ := Hag2
  subst hD hg
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
  let D' : StableAbs := { X.D with ints := X.D.ints.insert kb v }
  iunfold durCoreB at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, Hst', H8, H9, -, H10, H11, H12, H13, H14⟩
  unfold stVS
  imod ghostVar_update_halves (D', X.A.staged) _ _ _ $$ Hst Hst' with ⟨Hst, Hst'⟩
  have hgetD : ∀ k, ((D'.ints.lookup k).getD (W64 0)) = (X.D.ints.lookup k).getD (W64 0) :=
    fun k => getD_insert_same _ kb k v _ h
  imod Hcl $$ %({ X with D := D' }) [H1 H2 H3 H4 H5 H6 Hst' H8 H9 H10 H11 H12 H13 H14] [HL HS HSS Hld]
    with Hv
  · iunfold durCoreB
    simp only
    iframe
    ipureintro
    obtain ⟨p1, p2, p3, p4, p5⟩ := Hp
    refine ⟨p1, p2, ?_, ?_, p5⟩
    · unfold voteMatches at p3 ⊢; rw [hgetD]; exact ⟨p3.1, p3.2⟩
    · unfold termDurOk at p4 ⊢; rw [hgetD]; exact p4
  · iunfold durStores
    simp only
    iframe
  obtain ⟨hA, hlat⟩ := HX
  simp only
  rw [hA, hlat]
  imodintro
  iapply HK $$ Hv Hsv Hst

theorem dghostVar_halves' {A : Type} [Pos.Countable A] (γ' : GName) (a : A) :
    dghostVar (GF := GF) γ' (DFrac.own 1) a ⊢
      dghostVar γ' (DFrac.own (1 : Qp).half) a ∗ dghostVar γ' (DFrac.own (1 : Qp).half) a := by
  have h := dghostVar_split (GF := GF) γ' a (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rw [DFrac.op_own, Qp.half_add_half] at h
  iintro H
  iapply h $$ H

/-- (hraft_robust R5) What the crash state keeps about its latest snapshot, with no install pending, as
persistent facts (`latFacts`). -/
theorem latestDur_facts (fx : GoInterfaceOk) (lat : SnapLatest) (pend : Option (Nat × Nat × GoString))
    (dp : Option DiscPend) (hp : pend = none) :
    isFSM fx γ i rc.fsmOwn rc.respP rc.snapP ∗ latestDur γ rc i lat pend dp ⊢
      latestDur γ rc i lat pend dp ∗ latFacts γ rc i lat := by
  subst hp
  iintro ⟨#Hfsm, Hld⟩
  rcases lat with _ | ⟨m, b⟩
  · iframe; unfold latFacts; itrivial
  unfold latestDur
  icases Hld with ⟨Hok, Hd⟩
  unfold latestOk
  icases Hok with ⟨#He, Hsp, #Hcf, %Hv⟩
  ihave #Hsp' := isFSM_snapP_persistent fx γ i rc.fsmOwn rc.respP rc.snapP _ b $$ [Hfsm Hsp]
  · iframe #; iexact Hsp
  icases Hd with (%Hn | ⟨%m', %b', %Hmb, Hd⟩)
  · cases Hn
  cases Hmb
  icases Hd with (⟨#Hd, %Hdn⟩ | ⟨#Hsf, %Hdp, Ha⟩)
  · isplitr
    · isplitr
      · dsimp only; iframe #; ipureintro; exact Hv
      iright; iexists m, b
      isplitr; · ipureintro; rfl
      ileft; iframe #; ipureintro; exact Hdn
    unfold latFacts; dsimp only
    iframe #
    ipureintro; exact ⟨Hv.1, Hv.2.2.2⟩
  · isplitl [Ha]
    · isplitr
      · dsimp only; iframe #; ipureintro; exact Hv
      iright; iexists m, b
      isplitr; · ipureintro; rfl
      iright; iframe #
      isplitr; · ipureintro; exact Hdp
      iexact Ha
    unfold latFacts; dsimp only
    iframe #
    ipureintro; exact ⟨Hv.1, Hv.2.2.2⟩

/-- (hraft_robust R5) **The snapshot store during the boot, as `restoreSnapshot` reads it**: an atomic read
of the pinned latest, which also gives what the crash state keeps about it (`latFacts`; no install pending:
the main goroutine's half of `pend`). -/
theorem bootSnapAcc (fx : GoInterfaceOk) (A : LogAbs) (lat : SnapLatest) :
    srvDurInvRaw γ rc i ∗ isFSM fx γ i rc.fsmOwn rc.respP rc.snapP ⊢
    □ (bootV rc A lat ∗ ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) -∗
      |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old, rc.ownSS old ∗ ⌜old = lat⌝ ∗
        (rc.ownSS old ={∅, ⊤ \ ↑storeN}=∗
          (bootV rc A lat ∗ ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString))) ∗
          latFacts γ rc i lat)) := by
  iintro ⟨#Hi, #Hfsm⟩ !> ⟨Hv, Hpe⟩
  iapply ncfupd_bind
  isplitl [Hv]
  · iapply (bootOpen γ rc i (E := ⊤ \ ↑storeN) boot_dur_storeN A lat) $$ [Hv]
    iframe #; iframe
  iintro ⟨%X, %HX, Hc, Hs, Hcl⟩
  iunfold durCoreB at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, %Hp, H10, Hpe', H12, H13, H14⟩
  icombine Hpe Hpe' gives %Hag
  have hpe : X.pend = none := Hag.2.symm
  iapply ncfupd_of_fupd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hld⟩
  obtain ⟨hA, hlat⟩ := HX
  subst hA hlat
  iexists _
  iframe HSS
  isplitr
  · ipureintro; rfl
  iintro HSS
  imod Hmask with -
  -- the persistent facts of the latest
  ihave ⟨Hld, #Hlf⟩ := latestDur_facts γ rc i fx X.lat X.pend X.dp hpe $$ [Hld]
  · iframe #; iexact Hld
  imod Hcl $$ %X [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hpe' H12 H13 H14] [HL HS HSS Hld] with Hv
  · iunfold durCoreB; iframe; ipureintro; exact Hp
  · iunfold durStores; iframe
  imodintro
  iframe
  iframe #

theorem durN_diff_appliedN : (↑durN : CoPset) ⊆ ⊤ \ ↑appliedN := by
  unfold durN appliedN raftN; solve_ndisj

/-- (hraft_robust R5) **`setLastApplied(x)` while a discard is pending** (`NewRaft`'s restore of the
snapshot `d.x = x`): the main goroutine's half of the `lastApplied` authority is in the crash state
(`latestDur`'s discard-pending case); the store raises both halves to `x` and puts it back. -/
theorem setLastApplied_dp (r : Loc) (A : LogAbs) (lat : SnapLatest) (s : SState) (tp : Option TermPend)
    (d : DiscPend) (m0 : SnapshotMeta) (b0 : List w8) (hlat0 : lat = some (m0, b0)) (Φ : val → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ appliedCell r rc ∗ srvDurInvRaw γ rc i ∗
      bootV rc A lat ∗ srvVP rc s tp (some d) ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      (bootV rc A lat -∗ srvVP rc s tp (some d) -∗
        ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) -∗
        applLb rc (uint.nat m0.Index') -∗ Φ #()) ⊢
    WP (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setLastApplied")) (Val #m0.Index')) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hcell, #Hi, Hv, Hsv, Hpe, HK⟩
  wp_method_call; wp_call
  wp_method_call; wp_call
  wp_auto
  wp_apply_core boot_wp_StoreUint64_nc _ _ $$ [] [-]
  · iPkgInit
  iintro Hnc
  unfold appliedCell
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hcell with ⟨Hc0, Hcl0⟩
  ihave Hb := bootOpen γ rc i (E := ⊤ \ ↑appliedN) durN_diff_appliedN A lat $$ [Hv]
  · iframe #; iframe
  imod Hb $$ Hnc with ⟨Hnc, %X, %HX, Hc, Hs, Hcl⟩
  ihave ⟨Hc, %Hp⟩ := durCoreB_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCoreB_srvVP_agree γ rc i X s tp (some d) $$ [Hc Hsv]
  · iframe
  iunfold durCoreB at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, -, H10, Hpe', H12, H13, H14⟩
  icombine Hpe Hpe' gives %Hpg
  have hpe : X.pend = none := Hpg.2.symm
  obtain ⟨m, b, hlat, hmi, hmt⟩ := Hp.2.2.2.2.2.2.2.2 d Hag.2.2
  have hm0 : m = m0 ∧ b = b0 := by
    have := HX.2; rw [hlat, hlat0] at this; simp only [Option.some.injEq, Prod.mk.injEq] at this; exact this
  obtain ⟨rfl, rfl⟩ := hm0
  have hx : uint.nat m.Index' = d.x := hmi
  iframe Hnc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hc0 with ⟨%a, Hpt, Hca⟩
  iexists a
  iframe Hpt
  iintro Hpt
  iunfold durStores at Hs
  icases Hs with ⟨HL, HS, HSS, Hld⟩
  rcases X with ⟨Xs, XA, Xlo, Xc, XD, Xtp, Xlat, Xpend, Xdp⟩
  simp only at hpe hlat Hag ⊢
  subst hpe hlat
  obtain ⟨-, -, hdp⟩ := Hag
  subst hdp
  unfold latestDur
  icases Hld with ⟨Hok, Hd⟩
  icases Hd with (%Hn | ⟨%m', %b', %Hmb, Hd⟩)
  · cases Hn
  cases Hmb
  icases Hd with (⟨-, %Hdn⟩ | ⟨#Hsf, %Hdp, %a', Ha', %Ha'le⟩)
  · cases Hdn
  imod applied_halves_update rc a' (uint.nat a) (uint.nat m.Index') (by omega) $$ [Ha' Hca] with ⟨-, Ha', Hca⟩
  · iframe
  ihave #Hlb := monoNatLbOwn_get _ _ _ $$ Hca
  imod Hmask with -
  imod Hcl $$ %(⟨Xs, XA, Xlo, Xc, XD, Xtp, some (m, b), none, some d⟩ : SrvDur)
    [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hpe' H12 H13 H14] [HL HS HSS Hok Hsf Ha'] with Hv
  · iunfold durCoreB; iframe; ipureintro; exact Hp
  · iunfold durStores; iframe; unfold latestDur; iframe
    iright; iexists m, b
    isplitr; · ipureintro; rfl
    iright; iframe #
    isplitr; · ipureintro; exact Hdp
    iexists (uint.nat m.Index'); iframe; ipureintro; omega
  imod Hcl0 $$ [Hpt Hca] with -
  · inext; iexists m.Index'; iframe
  imodintro
  simp only at HX
  obtain ⟨hA, -⟩ := HX
  subst hA hlat0
  wp_auto
  iapply HK $$ Hv Hsv Hpe
  unfold applLb; iexact Hlb

section gp
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- (hraft_robust R5) **A durable index's entry is the committed one**: with `durLb x`, the server's log holds
at `x` the committed entry there. -/
theorem srvOwn_ent_durLb {E : CoPset} (hE : ↑gprotN ⊆ E) (s : SState) (x : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ durLb γ i x ∗ CIdx γ x e ⊢ |={E}=>
      srvOwn γ i s ∗ ⌜ent s.log x = some e ∧ x ≤ s.dur.1 ∧ s.dur.1 ≤ s.log.length⌝ := by
  iintro ⟨#HI, Hs, #Hd, #Hc⟩
  imod gprot.durLb_le γ E hE i s x $$ [$HI $Hs $Hd] with ⟨Hs, %hx⟩
  imod gprot.srvOwn_facts γ E hE i s $$ [$HI $Hs] with ⟨Hs, -, %Hf⟩
  imod gprot.srvOwn_CLb γ E hE i s $$ [$HI $Hs] with ⟨Hs, #HL⟩
  ihave #Hc' := Hc
  iunfold gprot.CIdx at Hc'
  icases Hc' with ⟨%h1, #Hm⟩
  have hdl : s.dur.1 ≤ s.log.length := Hf.2.1
  have hlen : (s.log.take s.dur.1).length = s.dur.1 := by simp; omega
  obtain ⟨e', he'⟩ := proto.ent_isSome (s.log.take s.dur.1) x h1 (by omega)
  ihave #HC' := gprot.CLb_idx γ _ x e' he' $$ HL
  iunfold gprot.CIdx at HC'
  icases HC' with ⟨-, #Hm'⟩
  ihave %Heq := mono_list_idx_agree γ.C (x - 1) e' e $$ Hm' Hm
  subst Heq
  iframe
  ipureintro
  refine ⟨?_, hx, hdl⟩
  rw [← proto.ent_take s.log s.dur.1 x hx]; exact he'

end gp

end boot

end github_com.hashicorp.raft

end Perennial
