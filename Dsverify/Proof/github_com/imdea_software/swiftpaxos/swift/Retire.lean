/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Retire.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**A goroutine's entry back to its owner, ghost part** (round 35, sv-swb; table rev 7 §3.11
T16a/T19, D36; notes/prove-swift.md §43): inside `descInv`'s opening at the `Remove` (T16a) or the
stop (T19), the entry's `descGo` gives the goroutine its halves back.

* `swift.incSt_live`: an incarnation's state with a quarter of its `γi` is live, with that key
  and descriptor.
* `swift.incInv_pin`: two committed incarnations, each with a quarter at the same key, are the
  same (`incInv`'s one live incarnation per key; D36).
* `swift.descGo_take`: `descGo` (with its `incW γi' γsg'`, quarter of `γi'` and receipt half) and
  the goroutine's parts (`incW γi γsg`: round 40, table rev 10a §3R10.21 C2/40-1, from `kfK`'s go
  branch or the slot message's payload `MPi`; a quarter of `γi` and its receipt half, from `kfK`)
  give `γi'` = `γi`, `γsg'` = `γsg`, the receipt's value `(j, ¼)` (so `descGo`'s registry share is
  `γn j ↦{¼} false`), `γi` ½ (for `incInv`'s retirement or the rest record), the receipt deleted,
  and `descGo`'s fields; a stopping entry (P39-1) is refuted by three receipt halves.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DescKind
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

/-- An incarnation's state with a quarter of its `γi` (see the file header). -/
theorem swift.incSt_live (γi : GName) (Mc : GMap GoString GoInterface) (r : GoString × Loc × Bool)
    (k : GoString) (d : Loc) :
    swift.incSt γi Mc r ∗ ghostVar γi (1 : Qp).half.half (k, d) ⊢
      swift.incSt γi Mc r ∗ ghostVar γi (1 : Qp).half.half (k, d) ∗
        ⌜r.2.2 = true ∧ r.1 = k ∧ r.2.1 = d⌝ := by
  iintro ⟨Hs, Hv⟩
  have hQ : ¬ ((1 : Qp).half.half + 1 ≤ 1) := by rw [Qp.le_iff]; simp; grind
  unfold swift.incSt
  cases hl : r.2.2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icombine Hv Hs gives %Hc
    exfalso; exact hQ Hc.1
  · simp only [↓reduceIte]
    icases Hs with ⟨Hs, %Hmc⟩
    icombine Hv Hs gives %Hc
    obtain ⟨-, Heq⟩ := Hc
    iframe Hv Hs
    ipureintro
    have h1 := congrArg Prod.fst Heq
    have h2 := congrArg Prod.snd Heq
    simp only at h1 h2
    simp_all

/-- **One live incarnation per key** (D36; see the file header). -/
theorem swift.incInv_pin (g : swift.DescG) (Mc : GMap GoString GoInterface) (k : GoString)
    (d d' : Loc) (γi γi' γsg γsg' : GName) :
    swift.incInv g Mc ∗ swift.incW g γi γsg ∗ swift.incW g γi' γsg' ∗
      ghostVar γi (1 : Qp).half.half (k, d) ∗ ghostVar γi' (1 : Qp).half.half (k, d') ⊢
    swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (k, d) ∗
      ghostVar γi' (1 : Qp).half.half (k, d') ∗ ⌜γi = γi'⌝ := by
  iintro ⟨HI, #Hw, #Hw', Hv, Hv'⟩
  iunfold swift.incInv at HI
  icases HI with ⟨%I, %R, Ha, Hm, %Hu⟩
  iunfold swift.incW at Hw Hw'
  ihave %Hl := ghost_map_lookup $$ Ha Hw
  ihave %Hl' := ghost_map_lookup $$ Ha Hw'
  ihave ⟨Hs, Hback⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun j _ => swift.incSt j Mc (R j))
    (show Iris.Std.PartialMap.get? I γi = some γsg from Hl)).1 $$ Hm
  ihave ⟨Hs, Hv, %H1⟩ := swift.incSt_live γi Mc (R γi) k d $$ [Hs Hv]
  · iframe
  ihave Hm := Hback $$ Hs
  ihave ⟨Hs', Hback'⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun j _ => swift.incSt j Mc (R j))
    (show Iris.Std.PartialMap.get? I γi' = some γsg' from Hl')).1 $$ Hm
  ihave ⟨Hs', Hv', %H2⟩ := swift.incSt_live γi' Mc (R γi') k d' $$ [Hs' Hv']
  · iframe
  ihave Hm := Hback' $$ Hs'
  have hn : I !! γi ≠ none := by
    rw [show I !! γi = Iris.Std.PartialMap.get? I γi from rfl,
      show Iris.Std.PartialMap.get? I γi = some γsg from Hl]; simp
  have hn' : I !! γi' ≠ none := by
    rw [show I !! γi' = Iris.Std.PartialMap.get? I γi' from rfl,
      show Iris.Std.PartialMap.get? I γi' = some γsg' from Hl']; simp
  have heq : γi = γi' := Hu γi γi' hn hn' H1.1 H2.1 (by rw [H1.2.1, H2.2.1])
  iframe Hv Hv'
  isplitl
  · iunfold swift.incInv
    iexists I, R
    iframe Ha Hm
    ipureintro; exact Hu
  ipureintro; exact heq

/-- **The entry's `descGo` back to its goroutine** (T16a/T19; D36; see the file header). Round 38
(table rev 9 P1): `descGo`'s `msgs` is ¼; the caller takes the entry's outer part (`entS`'s `seq` ½,
`msgs` ¼) itself. Round 40 (table rev 10a): the caller's witness names its stop bag (`γsg`), and the
stop bag returned is at that name; the stopping alternative is refuted. -/
theorem swift.descGo_take (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString)
    (d : Loc) (y : swift.CommandId) (Mc : GMap GoString GoInterface)
    (J : GMap GName (Nat × Qp)) (γi γsg : GName) (j : Nat) (E : CoPset) :
    swift.descGo γn g str d y ∗ swift.incInv g Mc ∗ ghostMapAuth g.γj 1 J ∗
      swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ⊢
    |={E}=> swift.incInv g Mc ∗ ghostMapAuth g.γj 1 (J.delete γi) ∗
      ghostVar γi (1 : Qp).half (str y, d) ∗ ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      ∃ (a : Bool) (sc : Loc) (γc : ChanNames) (m : Loc),
        typedPointsto (swift.dfld d go!"active") a (DFrac.own (1 : Qp).half) ∗
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half) ∗ swift.bagW m (g.mp y) ∗
        swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
        (if a then
          iprop((swift.sgTok γsg ∨ ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true) ∗
              typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half))
        else typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half)) := by
  iintro ⟨Hg, HI, HJ, #Hw, Hv, Hr⟩
  iunfold swift.descGo at Hg
  icases Hg with ⟨%j', %qj, %a, %sc, %γc, %γsg', %m, %γi', Hel, #Hw', Hv', Hr', Hs, Hm,
    #Hmb, #Hsb, Hst⟩
  ihave ⟨HI, Hv, Hv', %Heq⟩ := swift.incInv_pin g Mc (str y) d d γi γi' γsg γsg' $$ [HI Hv Hv']
  · iframe HI Hw Hw' Hv Hv'
  subst Heq
  ihave %Hsg := swift.incW_agree g γi γsg γsg' $$ [Hw Hw']
  · iframe Hw Hw'
  subst Hsg
  ihave %Hjq := ghostMapElem_agree γi g.γj _ _ _ _ $$ Hr Hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hjq
  iunfold swift.goSt at Hst
  icases Hst with (⟨Ha, Hst⟩ | ⟨-, -, Hr2⟩)
  rotate_left
  · -- stopping (P39-1): three halves of the receipt
    iexfalso
    ihave Hrw := (ghostMapElem_halves g.γj γi (j, (1 : Qp).half.half)).2 $$ [Hr Hr']
    · iframe
    icombine Hrw Hr2 gives %Hc
    exfalso
    have := DFrac.valid_own_op Hc.1
    revert this
    have : (1 : Qp).val = 1 := rfl
    simp
  ihave Hrw := (ghostMapElem_halves g.γj γi (j, (1 : Qp).half.half)).2 $$ [Hr Hr']
  · iframe
  imod ghost_map_delete $$ HJ Hrw with HJ
  ihave Hvh := (ghostVar_split_half γi (1 : Qp).half (str y, d)).2 $$ [Hv Hv']
  · iframe
  imodintro
  iframe HI HJ Hvh Hel
  iexists a, sc, γc, m
  iframe
  iframe Hmb Hsb

/-- A half of a receipt as two quarters (round 40). -/
theorem swift.rcpt_quarters (γ : GName) (k : GName) (v : Nat × Qp) :
    ghostMapElem (GF := netDistGF) γ k (DFrac.own (1 : Qp).half) v ⊣⊢
      ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v ∗
        ghostMapElem γ k (DFrac.own (1 : Qp).half.half) v := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp).half]
  exact (ghostMapElem_fractional k γ v).fractional _ _

/-- **The stop arm's ghost take** (round 40; table rev 10 T19a.g/T19Ra, P39-1, rev 10a C1/B1/40-4):
the goroutine's request (its signal token, at the name its witness `incW γi γsg` agrees with the
entry's), its half of `active` (`true`) and its receipt half move the entry's `descGo` from
signalled to **stopping**: `active`'s other half to the goroutine (whole), a quarter of the receipt
deposited. Unsignalled is refuted by two signal tokens, stopping by the receipt's shares (½ + ½ +
¼), `a = false` by `active`'s agreement (C1). -/
theorem swift.descGo_stop (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString)
    (d : Loc) (y : swift.CommandId) (Mc : GMap GoString GoInterface) (γi γsg : GName) (j : Nat)
    (E : CoPset) :
    swift.descGo γn g str d y ∗ swift.incInv g Mc ∗ swift.incW g γi γsg ∗
      ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half) (j, (1 : Qp).half.half) ∗
      typedPointsto (swift.dfld d go!"active") true (DFrac.own (1 : Qp).half) ∗ swift.sgTok γsg ⊢
    |={E}=> swift.descGo γn g str d y ∗ swift.incInv g Mc ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
      swift.dfld d go!"active" ↦ true ∗ swift.sgTok γsg := by
  iintro ⟨Hg, HI, #Hw, Hv, Hr, Ha0, Hsg⟩
  iunfold swift.descGo at Hg
  icases Hg with ⟨%j', %qj, %a, %sc, %γc, %γsg', %m, %γi', Hel, #Hw', Hv', Hr', Hs, Hm,
    #Hmb, #Hsb, Hst⟩
  ihave ⟨HI, Hv, Hv', %Heq⟩ := swift.incInv_pin g Mc (str y) d d γi γi' γsg γsg' $$ [HI Hv Hv']
  · iframe HI Hw Hw' Hv Hv'
  subst Heq
  ihave %Hsg := swift.incW_agree g γi γsg γsg' $$ [Hw Hw']
  · iframe Hw Hw'
  subst Hsg
  ihave %Hjq := ghostMapElem_agree γi g.γj _ _ _ _ $$ Hr Hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hjq
  iunfold swift.goSt at Hst
  icases Hst with (⟨Ha, Hst⟩ | ⟨-, -, Hr2⟩)
  rotate_left
  · -- stopping: the receipt's ½ + ½ + ¼
    iexfalso
    ihave Hrw := (ghostMapElem_halves g.γj γi (j, (1 : Qp).half.half)).2 $$ [Hr Hr']
    · iframe
    icombine Hrw Hr2 gives %Hc
    exfalso
    have := DFrac.valid_own_op Hc.1
    revert this
    have : (1 : Qp).val = 1 := rfl
    simp
  cases a
  · -- `a = false` (dead, PF21): `active`'s agreement (C1)
    iexfalso
    ihave ⟨%Hc, -⟩ := typedPointsto_half_combine _ true false (1 : Qp) $$ [Ha0 Ha]
    · iframe
    cases Hc
  simp only [↓reduceIte]
  icases Hst with ⟨(Hsg' | Hel2), Hsc⟩
  · -- unsignalled: two signal tokens
    iexfalso
    iunfold swift.sgTok at Hsg Hsg'
    icombine Hsg Hsg' gives %Hc
    obtain ⟨Hq, -⟩ := Hc
    exfalso
    have hQ1 : ¬ ((1 : Qp) + 1 ≤ 1) := by rw [Qp.le_iff]; simp; grind
    exact hQ1 Hq
  -- signalled → stopping
  ihave ⟨-, Ha⟩ := typedPointsto_half_combine _ true true (1 : Qp) $$ [Ha0 Ha]
  · iframe
  icases (swift.rcpt_quarters g.γj γi (j, (1 : Qp).half.half)).1 $$ Hr with ⟨Hr1, Hr2⟩
  imodintro
  iframe HI Hv Hr1 Ha Hsg
  iunfold swift.descGo
  iexists j, (1 : Qp).half.half, true, sc, γc, γsg, m, γi
  iframe Hel Hw Hv' Hr' Hs Hm Hmb Hsb
  iunfold swift.goSt
  iright
  iframe Hel2 Hsc Hr2

/-- **The home step's take** (round 40; table rev 10 T19h/T19Rh, P39-1, rev 10a 40-4): from a
stopping entry (others refuted by the goroutine's whole `active`), the goroutine's kept quarter of
the receipt agrees its value `(j, ¼)`; the receipt is deleted (½ + ¼ + ¼); `γi` ½ (for the rest
record), `descGo`'s registry quarter at the goroutine's `j`, its fields, the element's half and
`stopChan`'s half come out. -/
theorem swift.descGo_takeStop (γn : GName) (g : swift.DescG) (str : swift.CommandId → GoString)
    (d : Loc) (y : swift.CommandId) (Mc : GMap GoString GoInterface)
    (J : GMap GName (Nat × Qp)) (γi γsg : GName) (j : Nat) (a0 : Bool) (E : CoPset) :
    swift.descGo γn g str d y ∗ swift.incInv g Mc ∗ ghostMapAuth g.γj 1 J ∗
      swift.incW g γi γsg ∗ ghostVar γi (1 : Qp).half.half (str y, d) ∗
      ghostMapElem g.γj γi (DFrac.own (1 : Qp).half.half) (j, (1 : Qp).half.half) ∗
      swift.dfld d go!"active" ↦ a0 ⊢
    |={E}=> swift.incInv g Mc ∗ ghostMapAuth g.γj 1 (J.delete γi) ∗
      ghostVar γi (1 : Qp).half (str y, d) ∗ ghostMapElem γn j (DFrac.own (1 : Qp).half.half) false ∗
      swift.dfld d go!"active" ↦ a0 ∗
      ∃ (sc : Loc) (γc : ChanNames) (m : Loc),
        typedPointsto (swift.dfld d go!"seq") false (DFrac.own (1 : Qp).half.half) ∗
        typedPointsto (swift.dfld d go!"msgs") m (DFrac.own (1 : Qp).half.half) ∗ swift.bagW m (g.mp y) ∗
        swift.stopBag γc sc (swift.stopMP g.γs γsg (str y) d sc) ∗
        ghostMapElem g.γs (str y) (DFrac.own (1 : Qp).half) true ∗
        typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own (1 : Qp).half) := by
  iintro ⟨Hg, HI, HJ, #Hw, Hv, Hr, Ha0⟩
  iunfold swift.descGo at Hg
  icases Hg with ⟨%j', %qj, %a, %sc, %γc, %γsg', %m, %γi', Hel, #Hw', Hv', Hr', Hs, Hm,
    #Hmb, #Hsb, Hst⟩
  ihave ⟨HI, Hv, Hv', %Heq⟩ := swift.incInv_pin g Mc (str y) d d γi γi' γsg γsg' $$ [HI Hv Hv']
  · iframe HI Hw Hw' Hv Hv'
  subst Heq
  ihave %Hsg := swift.incW_agree g γi γsg γsg' $$ [Hw Hw']
  · iframe Hw Hw'
  subst Hsg
  ihave %Hjq := ghostMapElem_agree γi g.γj _ _ _ _ $$ Hr Hr'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj Hjq
  iunfold swift.goSt at Hst
  icases Hst with (⟨Ha, -⟩ | ⟨Hel2, Hsc, Hr2⟩)
  · -- not stopping: `active`'s half against the goroutine's whole
    iexfalso
    iapply swift.bool_pt_excl _ a0 a (1 : Qp).half $$ [Ha0 Ha]
    iframe
  ihave Hrh := (swift.rcpt_quarters g.γj γi (j, (1 : Qp).half.half)).2 $$ [Hr Hr2]
  · iframe
  ihave Hrw := (ghostMapElem_halves g.γj γi (j, (1 : Qp).half.half)).2 $$ [Hrh Hr']
  · iframe
  imod ghost_map_delete $$ HJ Hrw with HJ
  ihave Hvh := (ghostVar_split_half γi (1 : Qp).half (str y, d)).2 $$ [Hv Hv']
  · iframe
  imodintro
  iframe HI HJ Hvh Hel Ha0
  iexists sc, γc, m
  iframe Hs Hm Hmb Hsb Hel2 Hsc

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos
