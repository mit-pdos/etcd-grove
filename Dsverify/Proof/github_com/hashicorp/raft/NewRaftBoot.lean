/-
(hraft_robust R5) **The crash invariant during `NewRaft`** (the boot): opening the raw invariant with the
boot pin's other half, which fixes the stores' state the restore reads (`X.A`, `X.lat`), and ending the boot
(the pin discarded at `none`: `bootOver`, so that `srvDurInv` holds). A defs module of `NewRaft`'s proof.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash
public import Dsverify.Proof.github_com.hashicorp.raft.NewRaftRec

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
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  ihave ⟨Hc, %Hp⟩ := durCore_pure γ rc i X $$ Hc
  ihave ⟨Hc, Hsv, %Hag⟩ := durCore_srvVP_agree γ rc i X s tp dp $$ [Hc Hsv]
  · iframe
  ihave ⟨Hc, Hst, %Hag2⟩ := durCore_stVS_agree γ rc i X D g $$ [Hc Hst]
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
  iunfold durCore at Hc
  icases Hc with ⟨H1, H2, H3, H4, H5, H6, Hst', H8, H9, -, H10, H11, H12, H13, H14⟩
  unfold stVS
  imod ghostVar_update_halves (D', X.A.staged) _ _ _ $$ Hst Hst' with ⟨Hst, Hst'⟩
  have hgetD : ∀ k, ((D'.ints.lookup k).getD (W64 0)) = (X.D.ints.lookup k).getD (W64 0) :=
    fun k => getD_insert_same _ kb k v _ h
  imod Hcl $$ %({ X with D := D' }) [H1 H2 H3 H4 H5 H6 Hst' H8 H9 H10 H11 H12 H13 H14] [HL HS HSS Hld]
    with Hv
  · iunfold durCore
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
  iunfold durCore at Hc
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
  ihave #Hlf : (latFacts γ rc i X.lat : IProp GF) $$ [Hld]
  · rw [hpe]
    unfold latestDur latFacts
    rcases hl : X.lat with _ | ⟨m, b⟩
    · itrivial
    · icases Hld with ⟨Hok, Hd⟩
      unfold latestOk
      icases Hok with ⟨#He, Hsp, #Hcf, %Hv⟩
      ihave #Hsp' := isFSM_snapP_persistent fx γ i rc.fsmOwn rc.respP rc.snapP _ b $$ [Hfsm Hsp]
      · iframe #; iexact Hsp
      icases Hd with (%Hn | ⟨%m', %b', %Hmb, Hd⟩)
      · cases Hn
      cases Hmb
      icases Hd with (#Hd | ⟨#Hd, -⟩)
      · dsimp only; iframe #; ipureintro; exact ⟨Hv.1, Hv.2.2.2⟩
      · dsimp only; iframe #; ipureintro; exact ⟨Hv.1, Hv.2.2.2⟩
  imod Hcl $$ %X [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hpe' H12 H13 H14] [HL HS HSS Hld] with Hv
  · iunfold durCore; iframe; ipureintro; exact Hp
  · iunfold durStores; iframe
  imodintro
  iframe
  iframe #

end boot

end github_com.hashicorp.raft

end Perennial
