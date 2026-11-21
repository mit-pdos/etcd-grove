/-
**Crash adequacy with the extensions' state at each generation's start** (wal-safe, 2026-11-21;
`notes/wal-units/tester.md`, twelfth session; `notes/perennial-changes.md`, "Extension state access at
generation start"). A local copy of Perennial's `goose_crash_adequacy` (with `goose_crash_adequacy_blang`
and `goose_crash_preservation`, `Perennial/GooseLang/CrashAdequacy.lean` at Perennial `d648cfe22`), with
**one change**: each generation's `Hwp` is given, before its WP and its crash frame are made, one update
of the extensions' local interpretation (`∀ w, extsLocalCtx w ={⊤}=∗ extsLocalCtx w ∗ …`). The adequacy
proof holds the state interpretation there (after `goose_init`, and after `goose_crash_step`), so it can
give it. The executions, the hypotheses on them and the conclusion are `goose_crash_adequacy`'s; only
what a generation's proof may do at its start grows.

What it is for: the Linux file extension's mode switch (`treeCtx_switchG`) needs the extension's local
interpretation. With this, every generation switches before its WP, so its crash frame can already hold
what the shared mode lets it allocate (`AdequacyShared.lean`). Without it, the first switch happens at a
step, and a crash frame cannot take anything the switch made: the frame gets no later, since crashes
need not be separated by steps. A proposed Perennial change; this copy goes once Perennial has it.
Untrusted.
-/
module

public import Perennial.GooseLang.CrashAdequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

attribute [local instance] GSet.lawfulSet

section crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

/-- One update of the extensions' local interpretation inside the state interpretation. -/
theorem bstate_extsLocal_acc [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF] (s : BcfgState)
    (κs : List Observation) (X : IProp GF) :
    ⊢ gooseBstateInterp s κs -∗ (∀ w, extsLocalCtx (L := L) w ={⊤}=∗ extsLocalCtx (L := L) w ∗ X)
      ={⊤}=∗ gooseBstateInterp s κs ∗ X := by
  unfold gooseBstateInterp gooseStateInterp
  iintro ⟨⟨Hh, Hext, Hgs, %Hl, Hg, Hp⟩, Hr, Ht, Hnc⟩ Hk
  imod Hk $$ %_ Hext with ⟨Hext, HX⟩
  imodintro
  iframe
  ipureintro; exact Hl

/-- `goose_crash_preservation`, the boot premise given the new generation's extensions' local
interpretation for one update. -/
theorem goose_crash_preservation_acc [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF]
    (e : Expr) (T : Nat) (lctx : GoLocalContext) (φ : val → Prop)
    (Ψ : GooseLocalGS GF → IProp GF)
    (Hboot : ∀ (L L' : GooseLocalGS GF),
      @ThreadGS.threadBound GF L'.goose_threadGS = T →
      L'.goose_go_local_context = lctx →
      ⊢ Ψ L -∗ crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ threadTok (hT := L'.goose_threadGS) ={⊤}=∗
        ∀ w, extsLocalCtx (L := L') w ={⊤}=∗ extsLocalCtx (L := L') w ∗
          WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ L')
    {n : Nat} {ρ ρ' : List Expr × BcfgState} {κs : List Observation} {b : Bool}
    (H : BoundedCrashNsteps e T n ρ κs ρ' b) :
    ∀ (L : GooseLocalGS GF) (κs' : List Observation) (k : Nat),
      @ThreadGS.threadBound GF L.goose_threadGS = T → L.goose_go_local_context = lctx →
      ⊢ gooseBstateInterp ρ.2 (κs ++ κs') -∗ £ n -∗
        gooseWptp ρ.1 ((fun v => iprop(⌜φ v⌝)) :: forkPosts k) -∗ Ψ L
        ={⊤,∅}=∗ |={∅}▷=>^[n] |={∅,⊤}=> ∃ (L' : GooseLocalGS GF) (k' : Nat),
          gooseBstateInterp (L := L') ρ'.2 κs' ∗
          gooseWptp (L := L') ρ'.1 ((fun v => iprop(⌜φ v⌝)) :: forkPosts k') := by
  induction H with
  | done H =>
    intro L κs' k _ _
    iintro Hσ Hcred Hwp _
    imod goose_wptp_preservation H κs' _ $$ Hσ Hcred Hwp with H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%nt', Hσ, Hwp⟩
    imodintro
    iexists L, k + nt'
    iframe Hσ
    simp only [forkPosts, List.cons_append, List.replicate_append_replicate]
    iexact Hwp
  | @crash n m ρ κs t σ g f σ' κs₂ ρ' b H₁ hc _ ih =>
    intro L κs' k HT Hlctx
    have hT : 1 < T := HT ▸ L.goose_threadGS.threadBound_gt
    iintro Hσ Hcred Hwp HΨ
    rw [List.append_assoc]
    icases lc_split.1 $$ Hcred with ⟨Hcred₁, Hcred₂⟩
    imod goose_wptp_preservation H₁ (κs₂ ++ κs') _ $$ Hσ Hcred₁ Hwp with H
    imodintro
    rw [(step_fupdN_add (n := n) (m := m)).to_eq]
    iapply step_fupdN_wand $$ H
    iintro H
    iapply fupd_step_fupdN_absorb
    imod H with ⟨%nt', Hσ, -⟩
    imod goose_crash_step (L := L) T hT hc g f (κs₂ ++ κs') $$ Hσ
      with ⟨%L', %HL'lctx, %HL'T, Hσ, Hcr, Hcs, Hgs, Htok⟩
    imod Hboot L L' HL'T (by rw [HL'lctx, Hlctx]) $$ HΨ Hcr Hcs Hgs Htok with Hk
    imod bstate_extsLocal_acc (L := L') _ _ _ $$ Hσ Hk with ⟨Hσ, Hwp, HΨ⟩
    imod ih L' κs' 0 HL'T (by rw [HL'lctx, Hlctx]) $$ Hσ Hcred₂ [Hwp] HΨ with H
    · simp only [forkPosts, List.replicate_zero]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Hwp
    imodintro
    iexact H

/-- `goose_crash_adequacy_blang` with `Hwp` given the extensions' local interpretation for one update
(see the file header). -/
theorem goose_crash_adequacy_blang_acc [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok -∗
        ∀ w, extsLocalCtx (L := hG.goose_localGS) w ={⊤}=∗ extsLocalCtx (L := hG.goose_localGS) w ∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : BcfgState} {b : Bool}
    (Hsteps : BoundedCrashNsteps e T n ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) κs
      (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := n + 1)
  rw [(laterN_succ_right _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness .hasLC n ⊤
  iintro %Hinv Hf
  -- the crash frame of a generation is its guarantee that `P` holds after its crash
  let Ψ : HeapGS .hasLC GF → IProp GF := fun hG =>
    iprop(∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
      extsCrashStart hG.goose_localGS L' -∗
      ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ @P hG.goose_globalGS L')
  -- the first generation: `P` and the main thread's token (the change: the WP is made below, with
  -- the state interpretation)
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (hG : HeapGS .hasLC GF) => iprop(
      ⌜receiptBound GF = N ∧ threadBound GF = T ∧
        hG.goose_localGS.goose_go_local_context = σ.goState.goLctx⌝ ∗
      P hG.goose_localGS ∗ threadTok))
    (@fun hG HinvEq HN HT Hlctx => by
      subst HinvEq
      iintro Hg Hl Hgs Htok
      imod Hstart (hG := hG) HN HT Hlctx $$ Hg Hl Hgs with HP
      imodintro
      iframe
      ipureintro; exact ⟨HN, HT, Hlctx⟩)
    with ⟨%hG, %HinvEq, Hσ, %⟨HN, HT, Hlctx⟩, HP, Htok⟩
  ihave Hk := Hwp (hG := hG) HN HT Hlctx $$ HP Htok
  obtain ⟨⟨Ginv, Gall, Gproph, Gext, Grcpt⟩, L⟩ := hG
  cases HinvEq
  let G : GooseGlobalGS .hasLC GF := ⟨Ginv, Gall, Gproph, Gext, Grcpt⟩
  ihave H2 := bstate_extsLocal_acc _ _ _ $$ Hσ Hk
  imod H2 with ⟨Hσ, Hwp, HΨ⟩
  have Hboot : ∀ (L L' : GooseLocalGS GF),
      @ThreadGS.threadBound GF L'.goose_threadGS = T →
      L'.goose_go_local_context = σ.goState.goLctx →
      ⊢ Ψ ⟨G, L⟩ -∗ crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ threadTok (hT := L'.goose_threadGS) ={⊤}=∗
        ∀ w, extsLocalCtx (L := L') w ={⊤}=∗ extsLocalCtx (L := L') w ∗
          WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ ⟨G, L'⟩ := by
    intro L L' HT' Hlctx'
    iintro HΨ Hcr Hcs Hgs Htok
    imod HΨ $$ %L' Hcr Hcs Hgs with HP
    imodintro
    iapply Hwp (hG := ⟨G, L'⟩) HN HT' Hlctx' $$ HP Htok
  have Hpres := goose_crash_preservation_acc (G := G) e T σ.goState.goLctx φ (fun L => Ψ ⟨G, L⟩)
    Hboot Hsteps L [] 0 HT Hlctx
  rw [List.append_nil] at Hpres
  imod Hpres $$ Hσ Hf [Hwp] HΨ with H
  · simp only [gooseWptp, forkPosts, List.replicate_zero]
    iapply BigSepL2.bigSepL2_singleton.2
    iexact Hwp
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  iintro >⟨%L', %k', Hσ, Ht⟩
  iapply fupd_finally_keep iprop(⌜∀ e2, e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)⌝)
  isplit
  · iintro %e %Hin
    obtain ⟨i, He⟩ := List.getElem?_of_mem Hin
    icases BigSepL2.bigSepL2_lookup_left $$ Ht with ⟨%Φ', _, He⟩; exact He
    imod wp_not_stuck (iG := gooseIrisGS G L') (κs := []) (nt := 0) (ns := 0) $$ Hσ He with %_
    itrivial
  iintro %Hns
  imod wptp_postconditions (iG := gooseIrisGS G L') $$ Ht with Ht
  icases BigSepL2.bigSepL2_cons_inv_right $$ Ht with ⟨%e0, %t2', %Heq, He0, Ht2'⟩
  subst Heq
  icases BigSepL2.bigSepL2_length $$ Ht2' with %Hlen
  rw [List.length_replicate] at Hlen
  subst Hlen
  icases BigSepL2.bigSepL2_replicate_right $$ Ht2' with Ht2'
  icases bigSepL_toVal_pure t2' (fun v => v.isPanic = false) $$ Ht2' with %Hforks
  suffices Hm : (toVal e0).elim iprop(True) (fun v => iprop(⌜φ v⌝)) ⊢@{IProp GF}
      ⌜∀ v, e0 = Val v → φ v⌝ by
    icases Hm $$ He0 with %Hm
    ipureintro
    refine ⟨fun v t2'' h => ?_, Hns, fun v hv => ?_⟩
    · cases h; exact Hm v rfl
    · rcases List.mem_cons.1 hv with h | h
      · have := Hm v h.symm
        cases v <;> first | rfl | exact absurd this (hφ _)
      · exact Hforks v h
  cases e0 <;> simp only [toVal, Option.elim] <;>
    first
    | (iintro %H; ipureintro; rintro v ⟨⟩; exact H)
    | (iintro _; ipureintro; rintro v ⟨⟩)

/-- **`goose_crash_adequacy` with the extensions' state at each generation's start** (see the file
header): the same executions and conclusion; `Hwp` is given, before its WP and crash frame, one update
of the extensions' local interpretation. -/
theorem goose_crash_adequacy_acc [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok -∗
        ∀ w, extsLocalCtx (L := hG.goose_localGS) w ={⊤}=∗ extsLocalCtx (L := hG.goose_localGS) w ∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_crash_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  have H := goose_crash_adequacy_blang_acc N T (by omega) hT e σ g φ hφ Hinitg Hinit P Hstart Hwp Hb
  refine ⟨H.1, fun e2 he2 => realNotStuck_of_bounded (H.2.1 e2 he2), ?_⟩
  intro e2 He2 Hu
  obtain ⟨p, Hp⟩ := unrecoveredPanic_steps Hu
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem He2
  obtain ⟨m, κs', Hm⟩ := (Language.erasedStep_nSteps _ _).mp (Hp [] t₁ t₂ (σ2, ⟨c, t⟩))
  have := (goose_crash_adequacy_blang_acc N T (by omega) hT e σ g φ hφ Hinitg Hinit P Hstart Hwp
    (Hb.append Hm)).2.2 (PanicV p) (by simp)
  simp [val.isPanic] at this

end crash

end Perennial
