/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleStepN.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleProposal`'s ghost step with the leader's numbering (change log C22, M3, round 19, sv-swc):
`swift.handle_stepDN` is `swift.handle_stepD` (DescNode.lean) over `sp.upd_handleN`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescNode

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- `swift.handle_stepD` with the numbering (change log C22, M3): the run loop's node `k`, its
next number `n`, numbers `x` (`sp.upd_handleN`). -/
theorem swift.handle_stepDN (E : CoPset) (hE : ↑swift.nodeN ⊆ E) (hE' : ↑sp.spN ⊆ E \ ↑swift.nodeN)
    (γ : sp.Names) (γc γm γl γv γe γo : GName) {sn : swift.StN} (N r k : Nat) (fr : Bool)
    (l : List GoString) (w : swift.LView) (x : sp.CmdId) (c : sp.Cmd) (B : List sp.CmdId)
    (hr : r < N) (hk : nodeOf l r = some k) (hB : B <+: w.locAt w.1)
    (hx : x ∉ w.locAt w.1) (n : w64) (ld : Bool) (hld : ld = true ↔ sp.leaderOf N w.1 = r)
    (h0 : 0 ≤ sint.Z n) (hb : w.1 < 2 ^ 31) (hbc : w.2.1 = w.1) (W' : List w64) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ inv swift.nodeN (swift.nodeInvD γ γv γe γo sn k) ∗
      ghostVar γv (1 : Qp).half w ∗ sp.cmdIs γ x c ∗
      iprop(⌜w.1 = 0 ∧ B = []⌝ ∨ ∃ M, sp.syncIs γ w.1 M ∗ ⌜B = sp.syncOrder M⌝) ∗ sp.numHi γ k n ∗
      sp.predPre γ k (some (sp.PEv.handle w.1 x c, W')) ⊢
    |={E}=> ghostVar γv (1 : Qp).half (w.handled x) ∗
      sp.predPost γ k (some (sp.PEv.handle w.1 x c, W')) ∗
      sp.locAt γ r w.1 (w.locAt w.1).length x ∗ swift.claimTok sn.γcl (w.1, x) .fresh ∗
      sp.numIs γ r w.1 x (if ld then n else W64 (-1)) ∗ sp.numHi γ k (if ld then n + 1 else n) ∗
      ⌜ld = true → sint.Z (n + 1) = sint.Z n + 1⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hninv, Hw, #Hc, #HB, Hhi, Hpre⟩
  iinv Hninv with Hi Hclose
  iunfold swift.nodeInvD at Hi
  imod Hi
  icases Hi with ⟨%st, %O, Hst, Hw2, He, HO, HS, HX, %Hacc, %Hok⟩
  ihave %Heq := ghostVar_agree γv w (1 : Qp).half (swift.viewOf st) (1 : Qp).half $$ Hw Hw2
  subst Heq
  have hv1 : (swift.viewOf st).1 = st.ballot := rfl
  rw [hv1] at hB hx ⊢
  have hl : st.locAt st.ballot = (swift.viewOf st).locAt st.ballot := rfl
  imod sp.upd_handleN (E \ ↑swift.nodeN) hE' N fr l r k st x c n ld hr hk
    (by rw [hl]; exact hx) (by rw [← hv1]; exact hld) h0 hb W' $$ [Hst Hhi Hpre]
    with ⟨Hst, Hpost, Hl, #Hnum, Hhi, %Hov⟩
  · iframe Hinv Hcfg Hst Hc Hhi Hpre
    icases HB with (⟨%h0, %hB0⟩ | ⟨%M, #HM, %HBM⟩)
    · ileft; ipureintro; exact h0
    · iright; iexists M; isplitl []
      · iexact HM
      · ipureintro; rw [hl, ← HBM]; exact hB
  -- the new row token
  have hfresh : O.lookup (st.ballot, x) = none := by
    have hk := Hok st.ballot x
    revert hk
    rcases O.lookup (st.ballot, x) with _ | rv
    · intro _; rfl
    · intro hk; exact absurd hk.2 hx
  have hempty : swift.rowsOf st st.ballot x = swift.rowEmpty := by
    have hk := Hok st.ballot x; rw [hfresh] at hk; exact hk
  imod ghost_map_insert (st.ballot, x) swift.rowEmpty hfresh $$ HO with ⟨HO, Htok⟩
  -- round 32 (T28): the token goes into the store, the run loop gets a claim
  imod swift.storeD_mint γ γo sn st.cballot O (st.ballot, x) swift.rowEmpty .fresh hfresh hbc.symm
    $$ [HS Htok] with ⟨HS, Hcl⟩
  · iframe HS; unfold swift.rowTok; iframe Htok; simp only [swift.recOf, swift.retWhy]
    ipureintro; first | rfl | trivial
  have hview : swift.viewOf (st.handled st.ballot x) = (swift.viewOf st).handled x := rfl
  imod ghostVar_update_halves ((swift.viewOf st).handled x) γv (swift.viewOf st)
    (swift.viewOf st) $$ Hw Hw2 with ⟨Hw, Hw2⟩
  have hlocH : ∀ b y, y ∈ st.locAt b → y ∈ (st.handled st.ballot x).locAt b := by
    intro b y hy
    have : (st.handled st.ballot x).locAt b = (swift.viewOf (st.handled st.ballot x)).locAt b :=
      rfl
    rw [this, hview, swift.LView.handled_locAt]
    by_cases e : b = (swift.viewOf st).1
    · rw [if_pos e]; subst e; exact List.mem_append_left _ hy
    · rw [if_neg e]; exact hy
  imod Hclose $$ [Hst Hw2 He HO HS HX] with -
  · inext
    iunfold swift.nodeInvD
    iexists st.handled st.ballot x, O.insert (st.ballot, x) swift.rowEmpty
    iframe Hst HO
    isplitl [Hw2]
    · rw [hview]; iexact Hw2
    isplitl [He]
    · have hep : swift.epochOf (st.handled st.ballot x) = swift.epochOf st := rfl
      rw [hep]; iexact He
    isplitl [HS]
    · rw [show (st.handled st.ballot x).cballot = st.cballot from rfl]; iexact HS
    isplitl [HX]
    · iapply (swift.nodeX_mono γ sn st (st.handled st.ballot x) (Nat.le_refl _) rfl rfl
        (fun _ h => h)); iexact HX
    · ipureintro
      refine ⟨Hacc, fun b y => ?_⟩
      rw [GMap.lookup_insert_eq_iff]
      by_cases e : (st.ballot, x) = (b, y)
      · rw [if_pos e]; cases e
        refine ⟨hempty.symm, ?_⟩
        have : (st.handled st.ballot x).locAt st.ballot =
            (swift.viewOf (st.handled st.ballot x)).locAt st.ballot := rfl
        rw [this, hview, swift.LView.handled_locAt,
          if_pos hv1.symm]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [if_neg e]
        have hk := Hok b y
        revert hk
        rcases O.lookup (b, y) with _ | rv
        · intro hk; exact hk
        · intro hk; exact ⟨hk.1, hlocH b y hk.2⟩
  imodintro
  iframe Hw Hnum Hhi Hcl Hpost
  isplitl [Hl]
  · rw [← hl]; iexact Hl
  · ipureintro; exact Hov

/-- A whole points-to as two halves, both ways (as HandleProposeProof's `swift.pt_halves`). -/
theorem swift.pt_halvesR {V : Type} [TypedPointsto (GF := netDistGF) V] (l : Loc) (v : V) :
    (typedPointsto (V := V) l v (DFrac.own 1) : IProp netDistGF) ⊣⊢
      (typedPointsto (V := V) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (V := V) l v (DFrac.own (1 : Qp).half)) := by
  have h : (DFrac.own 1 : DFrac) = DFrac.own (1 : Qp).half • DFrac.own (1 : Qp).half := by
    rw [DFrac.op_own, Qp.half_add_half]
  rw [h]
  exact (typedPointsto_dfractional (GF := netDistGF) l v).dfractional _ _

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
