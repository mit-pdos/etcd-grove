/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Wg.lean`, run `rabia-r1wake-1`.)

The wait-group counting idiom of `Defs.lean` (`wgCtr`, `wgTok`): allocation, `Add(d)`, `Done()`.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia sync

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [sync.Assumptions]

/-- `d` routines' rights to call `Done`. -/
def wgToks (wg : Loc) (d : Nat) : IProp GF :=
  iprop(∃ γw γt γb, isWg wg γw γt γb ∗ ownToks γt d)

theorem wgToks_split (wg : Loc) (d : Nat) :
    wgToks (GF := GF) wg (d + 1) ⊢ wgTok wg ∗ wgToks wg d := by
  unfold wgToks wgTok
  iintro ⟨%γw, %γt, %γb, #Hwg, Ht⟩
  icases ownToks_add_1 1 d γt $$ Ht with ⟨Ht1, Ht2⟩
  isplitl [Ht2]
  · iexists γw, γt, γb; iframe Hwg Ht2
  · iexists γw, γt, γb; iframe Hwg Ht1

theorem wg_alloc (wg : Loc) (b : Nat) (hb : b ≤ wgMax) :
    typedPointsto (GF := GF) wg (zero_val WaitGroup) (DFrac.own 1) ⊢ |={⊤}=> wgCtr wg b := by
  iintro H
  imod init_WaitGroup (wgN.@"wg") wg $$ H with ⟨%γw, #His, Hctr, Hwait⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod ghostVar_alloc b with ⟨%γb, Hb⟩
  icases ghostVar_split γb b (1 : Qp).half (1 : Qp).half $$ [Hb] with ⟨Hb1, Hb2⟩
  · rw [Qp.half_add_half]; iexact Hb
  imod inv_alloc (wgN.@"inv") ⊤ (wgBody (GF := GF) γw γt γb) $$ [Hctr Hwait Ht Hb1] with #Hinv
  · inext
    unfold wgBody
    iexists (W32 0), 0, b
    iframe
    ipureintro
    exact ⟨by decide, by omega⟩
  imodintro
  unfold wgCtr isWg
  iexists γw, γt, γb
  iframe Hb2
  isplit <;> iassumption

theorem wp_wgAdd (wg : Loc) (b d : Nat) (hd : d ≤ b) (hd' : 0 < d) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wgCtr wg b }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 d)))
    {{ RET #(); wgCtr wg (b - d) ∗ wgToks wg d }} := by
  wp_start_folded as Ha
  unfold wgCtr isWg
  icases Ha with ⟨%γw, %γt, %γb, ⟨#His, #Hinv⟩, Hb⟩
  wp_apply_core sync.WaitGroup.wp_Add wg (W64 d) γw (wgN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgN "wg" "inv" (by decide))
  iintro Hmask
  inext
  unfold wgBody
  icases Hi with ⟨%ctr, %n, %b', Hctr, Hwait, Ht, Hb', %Hn⟩
  icombine Hb Hb' gives % ⟨_, Heq⟩
  subst Heq
  have hdmax : d ≤ wgMax := by omega
  have hdz : sint.Z (W32 (sint.Z (W64 d))) = d := by
    unfold wgMax at hdmax
    word
  iexists ctr
  iframe Hctr
  isplitr
  · ipureintro
    simp only [wgMax] at Hn ⊢
    omega
  iright
  iframe Hwait
  iintro Hwait Hctr
  imod Hmask with -
  imod ownTokAuth_add d γt n $$ Ht with ⟨Ht, Htoks⟩
  imod ghostVar_update_halves (b - d) γb b b $$ Hb Hb' with ⟨Hb, Hb'⟩
  imod Hclose $$ [Hctr Hwait Ht Hb'] with -
  · inext
    iexists (ctr + W32 (sint.Z (W64 d))), n + d, b - d
    iframe
    ipureintro
    simp only [wgMax] at Hn ⊢
    refine ⟨?_, by omega⟩
    rw [hdz] at *
    word
  imodintro
  iapply HΦ
  isplitl [Hb]
  · iexists γw, γt, γb
    iframe Hb
    isplit <;> iassumption
  · unfold wgToks isWg wgBody
    iexists γw, γt, γb
    iframe Htoks
    isplit <;> iassumption

theorem wp_wgDone (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ wgTok wg }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as Ha
  unfold wgTok isWg
  icases Ha with ⟨%γw, %γt, %γb, ⟨#His, #Hinv⟩, Htok⟩
  wp_apply_core sync.WaitGroup.wp_Done wg γw (wgN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgN "wg" "inv" (by decide))
  iintro Hmask
  inext
  unfold wgBody
  icases Hi with ⟨%ctr, %n, %b, Hctr, Hwait, Ht, Hb, %Hn⟩
  icombine Ht Htok gives %Hle
  iexists ctr
  iframe Hctr
  isplitr
  · ipureintro
    simp only [wgMax] at Hn ⊢
    omega
  iintro Hctr
  imod Hmask with -
  imod ownTokAuth_sub 1 γt n $$ Ht Htok with Ht
  imod Hclose $$ [Hctr Hwait Ht Hb] with -
  · inext
    iexists (ctr - W32 1), n - 1, b
    iframe
    ipureintro
    simp only [wgMax] at Hn ⊢
    refine ⟨?_, by omega⟩
    word
  imodintro
  iapply HΦ
  itrivial

end proofs

end Perennial.rabia.internal.tcp

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode sync sync.join

section join2
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [sync.Assumptions]

/-- The join idiom's `Add(2)` from a fresh adder: two `Done` permissions with `P1`, `P2`. -/
theorem wp_join_Add2 (wg : Loc) (P1 P2 : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg (W32 0) iprop(True) }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
    {{ RET #(); ownAdder wg (W32 2) iprop((True ∗ P1) ∗ P2) ∗ ownDone wg P1 ∗ ownDone wg P2 }} := by
  wp_start_folded as Ha
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.WaitGroup.wp_Add wg (W64 2) γ.wgGn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  subst Heq
  have h1 : sint.Z (W32 (sint.Z (W64 2))) = 2 := by decide
  have h2 : W32 (sint.Z (W64 2)) = W32 2 := by decide
  rw [h1, h2]
  have h0 : sint.nat (W32 0) = 0 := rfl
  rw [h0] at Hctr_inv
  isplitr
  · ipureintro
    simp only [sint.nat, sint.Z] at *
    omega
  iright
  iframe Hno_waiters
  iintro Hno_waiters Hwg_ctr_inv
  imod Hmask with -
  rw [h0]
  imod ownApropAuth_add P1 γ.wgApropGn P0 0 $$ Haprop with ⟨Haprop, Hd1⟩
  imod ownApropAuth_add P2 γ.wgApropGn _ (0 + 1) $$ Haprop with ⟨Haprop, Hd2⟩
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn 0).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht1⟩
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht2⟩
  icases (ownTokAuth_halves γ.wgNotDoneGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv] with -
  · inext
    iexists (ctr + W32 2), 0 + 1 + 1, done, Pdone
    iframe
    ipureintro
    simp only [sint.nat] at *
    constructor <;> word
  imodintro
  iapply HΦ
  simp only [ownAdder_unseal, ownAdderDef, ownDone_unseal, ownDoneDef]
  isplitl [Hno_waiters Haprop Hadded HimpliesP]
  · iexists γ, iprop((P0 ∗ P1) ∗ P2)
    rw [show sint.nat (W32 2) = 0 + 1 + 1 from rfl]
    iframe
    isplitr
    · ipureintro; decide
    isplitl
    · iintro ⟨⟨H0, H1⟩, H2⟩
      iframe H1 H2
    unfold isWgjInv named
    isplit <;> iassumption
  isplitl [Hd1 Ht1]
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption

end join2

end Perennial.rabia.internal.tcp
