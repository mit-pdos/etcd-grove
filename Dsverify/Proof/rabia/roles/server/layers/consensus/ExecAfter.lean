/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecAfter.lean`, run `rabia-r1wake-1`.)

The executor's AfterWaits (`phase0Round1AfterWait`, `phase0Round2AfterWait`,
`phaseNRound1AfterWait`, `phaseNRound2AfterWait`), against ExecDefs' specs: each reads the frozen
quorum of `n - f` messages of its round (`quorum_bits`, `quorum_props`), and records the fact the
code computes from it — the vote (`VoteOk`), the state (`StateOk`), or a decision (`DecEvidence`:
`f + 1` votes, `MajorityPlusF` states, `MajorityPlusF` proposals).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecFind

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section after
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

/-- The specification the AfterWaits need of `genDecMsgType2`. -/
abbrev gdSpec (γ : Names) (cf : RCfg) (c : Loc) : Prop :=
  ∀ (s : Nat) (v : ConsensusObj) (o : ObjV),
    {{ exPre (GF := GF) γ cf ∗ objRep v o }}
      (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genDecMsgType2"))
        (Val #(W32 s))) (Val #v))
    {{ (w : Msg), RET #w; msgRep w (decMsg o s) }}

/-- The decision's evidence of a frozen round of states (`MajorityPlusF`, `p ≥ 1`) or votes
(`f + 1`). -/
theorem bitEv_of (γ : Names) (t p r : Nat) (T : List Ent) (hS : Senders cf (bitPairs T))
    (hev : (r = 1 ∧ 1 ≤ p ∧ majT (valsOf T) ≥ cf.mpf) ∨ (r = 2 ∧ majT (valsOf T) ≥ cf.fp1)) :
    ([∗list] kv ∈ bitFacts t p r (bitPairs T), fact (GF := GF) γ.rab kv.1 kv.2) ⊢
      bitEvW γ cf t (majV (valsOf T)) := by
  iintro #HF
  unfold bitEvW
  iexists bitFacts t p r (bitPairs T)
  iframe HF
  ipureintro
  intro M _ _ hS' d hd
  have hf := bitFacts_mem hS'
  have e : valsOf T = (bitPairs T).map Prod.snd := (bitPairs_snd T).symm
  rw [e] at hd hev
  rcases hev with ⟨rfl, hp, hge⟩ | ⟨rfl, hge⟩
  · exact decEv_states hp hS (fun x hx => by simpa using hf x hx) hge hd
  · exact decEv_votes hS (fun x hx => by simpa using hf x hx) hge hd

theorem wp_phaseNRound1AfterWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hRPW : rpwSpec (GF := GF) γ cf k γl γc ch c) (hGD : gdSpec (GF := GF) γ cf c)
    (σ : ExSt) (x : ExSlot)
    (hx : x.pv.phase ≠ 0 ∧ x.pv.round = 1 ∧ x.ρs = exRound x.pv + 1)
    (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phaseNRound1AfterWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy x.pv.phase.toNat 2 bit with round := 2 }) v b }} := by
  wp_start as ⟨#Hpre, Hrun⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨#Hcff, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hcb := cf_bounds hcf
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  obtain ⟨hp0, hr1, hρs⟩ := hx
  have hp1 : 1 ≤ x.pv.phase.toNat := by
    have : x.pv.phase.toNat ≠ 0 := fun h => hp0 (by bv_omega)
    omega
  have hρ : exRound x.pv = 2 * x.pv.phase.toNat + (W32 1).toNat - 1 := by
    unfold exRound; rw [hr1]; rfl
  have hpr : ((W32 1).toNat = 1 ∧ 1 ≤ x.pv.phase.toNat) ∨ (W32 1).toNat = 2 :=
    Or.inl ⟨rfl, hp1⟩
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c σ.t e he $$ Hro
  imod quorum_bits γ k γl γc σ.t e he x.ql x.pv.phase.toNat (W32 1).toNat (exRound x.pv) hpr
    hρ hn $$ [Hsi Hql] with ⟨%ents0, #Hlb, ⟨%h0, %hS, %hlW⟩, #HF⟩
  · iframe Hsi Hql
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hts : (W32 σ.t).toNat = σ.t := by unfold lenLedger at ht; word
  have hs : (W32 σ.t).toNat < lenLedger := by rw [hts]; exact ht
  -- the frozen values
  have hvl : (valsOf (tally ents0 (exRound x.pv))).length = cf.q := by
    simp only [valsOf, List.length_map]; exact h0
  have hT := majT_le_length (valsOf (tally ents0 (exRound x.pv)))
  rw [hvl] at hT
  wp_auto
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c (W32 σ.t) hs $$ [$Hconf $Hro]
  try wp_auto
  have hmod : W32 σ.t % W32 10000 = W32 σ.t := by unfold lenLedger at ht; word
  rw [hmod]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl ht
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  ihave ⟨HPh, HRd, ⟨%mv, HMp, #Hmr⟩, %rest, Hrest, Hcl⟩ := (slotPriv_fields e.loc x.pv).1 $$ Hpriv
  wp_auto
  ihave Hpriv := Hcl $$ %x.pv.phase %x.pv.round %mv [HPh HRd HMp Hrest]
  · iframe; iexact Hmr
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he x.pv.phase (W32 1) (Or.inl rfl) hpr
    _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
  wp_auto
  by_cases hge : majT (valsOf (tally ents0 (exRound x.pv))) ≥ cf.mpf
  · -- decide (`MajorityPlusF` equal states)
    rw [decide_eq_true (by word)]
    wp_auto
    ihave Hrun := exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    ihave #Hev := bitEv_of γ σ.t x.pv.phase.toNat (W32 1).toNat _ hS
      (Or.inl ⟨rfl, hp1, hge⟩) $$ HF
    wp_apply (wp_findReturnValue_strong D γ k γl γc ch c hRPW σ { x with pv := x.pv } x.pv.phase
      (W32 1) (Or.inl rfl) hpr (valsOf (tally ents0 (exRound x.pv))) hq) $$ [$Hrun]
      as %m ⟨%σ', %x', %d, %o, Hrun, %hst, #Hm, #Hdo, #Hj⟩
    · isplitr
      · iexact Hpre
      isplitr
      · unfold notified; iexists x.ql; iframe Hql; ipureintro
        rw [← hρ]; exact hn
      isplitr
      · unfold frozenVals; iexists ents0; iframe Hlb; ipureintro
        rw [← hρ]; exact ⟨rfl, h0⟩
      · iexact Hev
    obtain ⟨hstep, hpv, hcur, hρs'⟩ := hst
    wp_apply (lc := 1) (hGD σ.t m o) $$ [$Hpre $Hm] as %w #Hw
    ihave ⟨%e', %hee', Hpriv, #Hro', #Hql', Hfr⟩ := exRun_split γ k γl γc ch c σ' x' $$ Hrun
    obtain ⟨he', ht', hmy'⟩ := hee'
    rw [hstep.1] at he'
    rw [he] at he'
    cases he'
    have hmd' : FKey.mydec k σ'.t ∉ x'.cur := by
      rw [hstep.1]
      rcases hcur with h | h <;> rw [h]
      · exact hmd
      · simp only [List.mem_cons, reduceCtorEq, _root_.false_or]; exact hmd
    imod frame_dec_commit γ k hk γl γc ch c σ' x' hmd' d $$ [Hsh Hcfg Hfr Hlc1 Hj] with
      ⟨Hfr, #Hmy, #Hdec⟩
    · iframe Hsh Hcfg Hfr Hlc1; rw [hstep.1]; iexact Hj
    ihave %hos := decObjOk_svrSeq γ σ.t d o $$ Hdo
    ihave #Hw' : msgRep w (decMsg o σ'.t) $$ [Hw]
    · rw [hstep.1]; iexact Hw
    ihave #Hdo' : decObjOk γ cf σ'.t d o $$ [Hdo]
    · rw [hstep.1]; iexact Hdo
    wp_apply (wp_toNet_dec γ k γl γc ch c { σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke }
      { x' with cur := FKey.mydec k σ'.t :: x'.cur } w o d (by rw [hstep.1]; exact hos)
      (by rw [hstep.1]; unfold lenLedger; exact ht)) $$ [$Hpk $Hfr $Hw' $Hdec $Hdo']
      as ⟨%L2, %sent2, Hfr⟩
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
      (slotPriv_fields e.loc _).1 $$ Hpriv
    try wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    try wp_auto
    ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
    · iframe; iexact Hmr2
    ihave Hrun := exRun_join γ k γl γc ch c
      ({ ({ σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke } : ExSt) with L := L2, sent := sent2 })
      ({ x' with cur := FKey.mydec k σ'.t :: x'.cur }) e
      ({ x'.pv with phase := x'.pv.phase, round := x'.pv.round + W32 1 })
      (by rw [hstep.1]; exact he) hmy' $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    iapply HΦ
    iexists (W32 0)
    unfold afterPost
    simp only [↓reduceIte]
    iexists _, _, d, o
    iframe Hrun
    isplitr
    · ipureintro
      exact ⟨⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2⟩,
        by simp [hstep.1]⟩
    unfold decidedW
    rw [← hstep.1]
    iframe Hmy Hdec Hdo'
    rw [hstep.1]
    iexact Hm
  · rw [decide_eq_false (by word)]
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he x.pv.phase (W32 1) (Or.inl rfl) hpr
      _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
    -- the vote and its justification
    let B : Nat := if majT (valsOf (tally ents0 (exRound x.pv))) ≥
      cf.maj then majV (valsOf (tally ents0 (exRound x.pv))) else 2
    have hB : B ≤ 2 := by
      show (if _ then _ else _) ≤ 2
      split
      · have := majV_le1 (valsOf (tally ents0 (exRound x.pv))); omega
      · omega
    ihave #Hjust : nextJust γ k σ.t ({ x.pv.setMy x.pv.phase.toNat 2 (W32 B) with round := 2 })
      $$ []
    · unfold nextJust
      rw [if_neg (by simp), if_pos rfl]
      unfold factJust
      iexists cfgFact cf :: bitFacts σ.t x.pv.phase.toNat (W32 1).toNat
        (bitPairs (tally ents0 (exRound x.pv)))
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe Hcff HF
      · ipureintro
        rw [PrivSt.my_with, PrivSt.setMy_phase, PrivSt.my_setMy _ _ _ _ (Or.inr rfl)]
        have hBn : (W32 B).toNat = B := by word
        rw [hBn]
        have := vote_valid (s := σ.t) (p := x.pv.phase.toNat) hk (by omega) hS hlW
        rw [bitPairs_snd] at this
        exact this
    wp_auto
    wp_if_destruct
    · slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajV_frozen D.bcMajV γ k γl γc σ.t e he x.pv.phase (W32 1) (Or.inl rfl)
        hpr _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      try wp_auto
      have hBv : B = majV (valsOf (tally ents0 (exRound x.pv))) := by
        show (if _ then _ else _) = _
        rw [if_pos (by word)]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv x.pv.phase (W32 2)
        (W32 (majV (valsOf (tally ents0 (exRound x.pv)))))
        (Or.inr rfl) $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy x.pv.phase.toNat 2 (W32 B)) $$ [Hpriv]
      · rw [hBv]; iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      try wp_auto
      have hr2 : x.pv.round + W32 1 = (2 : w32) := by rw [hr1]; rfl
      ihave Hpriv := Hcl $$ %_ %(2 : w32) %mv2 [HPh HRd HMp Hrest]
      · rw [← hr2]; iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy x.pv.phase.toNat 2 (W32 B) with round := 2 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy x.pv.phase.toNat 2 (W32 B) with round := 2 }) he (by
            rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
      iexact Hjust
    · have hBv : B = 2 := by
        show (if _ then _ else _) = _
        rw [if_neg (by word)]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv x.pv.phase (W32 2) (W32 2) (Or.inr rfl) $$ [$Hpl $Hpriv]
        as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy x.pv.phase.toNat 2 (W32 B)) $$ [Hpriv]
      · rw [hBv]; iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      try wp_auto
      have hr2 : x.pv.round + W32 1 = (2 : w32) := by rw [hr1]; rfl
      ihave Hpriv := Hcl $$ %_ %(2 : w32) %mv2 [HPh HRd HMp Hrest]
      · rw [← hr2]; iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy x.pv.phase.toNat 2 (W32 B) with round := 2 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy x.pv.phase.toNat 2 (W32 B) with round := 2 }) he (by
            rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
      iexact Hjust


/-- `genDecMsgType1(s)` of a frozen round 0: the decision message of its first sorted tally's
object. -/
theorem wp_genDecMsgType1_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames)
    (γc : ConsNames) (ch : SrvChans) (c : Loc) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (hs : s < lenLedger) (ents0 : List Ent) (h2 : (tally ents0 0).length = cf.q)
    (hne : objsOf (tally ents0 0) ≠ []) :
    {{ exPre (GF := GF) γ cf ∗ consRO γ cf k γl γc ch c ∗ monoListLbOwn (entName γl γc s) ents0 }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genDecMsgType1"))
        (Val #(W32 s)))
    {{ (w : Msg), RET #w;
        msgRep w (decMsg ((propHead (objsOf (tally ents0 0))).map (·.1)).get! s) }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, #Hro, #Hlb⟩
  wp_auto
  have hs' : (W32 (s : Int)).toNat < lenLedger := by unfold lenLedger at hs ⊢; word
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c _ hs' $$ [$Hpkg $Hconf $Hro]
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c s e he $$ Hro
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ [Hpkg]
  · iPkgInit
  unfold lenLedger at hs Hl
  wp_auto
  have hmod : W32 (s : Int) % W32 10000 = W32 (s : Int) := by word
  rw [hmod]
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (s : Int))))) _ _ e.loc (by word)
    $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (s : Int))))).toNat = s by word]
    simp [he]
  iapply wp_fupd
  wp_apply_core wp_propMajV_frozen D.majV γ k γl γc s e he ents0 h2 hne $$ Hlp Hse Hsi Hlb
  iintro %v #Hv
  wp_auto
  ipersist obj
  imodintro
  iapply HΦ
  iapply cons_msgRep_intro
  · simp [decMsg, tyDecision, Decision]
  simp only [decMsg]
  iexists { v with SvrSeq' := W32 (s : Int) }
  iframe obj
  iapply cons_objRep_svrSeq $$ Hv

theorem wp_phase0Round1AfterWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (σ : ExSt) (x : ExSlot)
    (hx : x.pv.phase = 0 ∧ x.pv.round = 1 ∧ x.ρs = 1) (hn : some 0 ∈ x.ql)
    (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phase0Round1AfterWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ((x.pv.setMy 0 2 bit) |> fun p => { p with round := 2 }) v b }} := by
  wp_start as ⟨#Hpre, Hrun⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨#Hcff, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hcb := cf_bounds hcf
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c σ.t e he $$ Hro
  imod quorum_props γ k γl γc σ.t e he x.ql ⟨0, Nat.le_refl _, hn⟩ $$ [Hsi Hql] with
    ⟨%ents0, #Hlb, ⟨%h0, %hS0, %hl0, %hsnd⟩, #HF0, #Hos⟩
  · iframe Hsi Hql
  have hne := objsOf_ne hcf hl0 hsnd
  obtain ⟨o, kk, hhead, hom, hkk, hmax⟩ := propHead_spec hne
  have hkq : kk ≤ cf.q := by
    have := List.count_le_length (a := objId o) (l := (objsOf (tally ents0 0)).map objId)
    rw [List.length_map] at this
    have h2 : (objsOf (tally ents0 0)).length = cf.q := by
      rw [← hl0, ← List.length_map (f := Prod.snd), hsnd, List.length_map]
    omega
  have hcnt : ∀ id, ((propPairs (tally ents0 0)).map Prod.snd).count id ≤ kk := by
    intro id; rw [hsnd]; exact hmax id
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hts : (W32 σ.t).toNat = σ.t := by unfold lenLedger at ht; word
  have hs : (W32 σ.t).toNat < lenLedger := by rw [hts]; exact ht
  wp_auto
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c (W32 σ.t) hs $$ [$Hconf $Hro]
  try wp_auto
  have hmod : W32 σ.t % W32 10000 = W32 σ.t := by unfold lenLedger at ht; word
  rw [hmod]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl ht
  obtain ⟨hp0, hr1, hρs⟩ := hx
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  wp_apply_core wp_propMajT_frozen D.majT γ k γl γc σ.t e he ents0 h0 hne $$ Hpl Hse Hsi Hlb
  rw [hhead]
  simp only [Option.map_some, Option.getD_some]
  wp_auto
  by_cases hge : kk ≥ cf.mpf
  · -- decide (`MajorityPlusF` proposals of one object)
    rw [decide_eq_true (by word)]
    wp_auto
    ihave ⟨#Hoo, %hos⟩ := (BigSepL.bigSepL_mem
      (Φ := fun o : ObjV => iprop(objOk (GF := GF) γ cf o ∗ ⌜o.svrSeq.toNat = σ.t⌝)) hom) $$ Hos
    wp_apply (lc := 1) (wp_genDecMsgType1_proof D γ k γl γc ch c σ.t e he ht ents0 h0 hne)
      $$ [$Hpre $Hro $Hlb] as %w #Hw
    rw [hhead]
    simp only [Option.map_some, Option.get!_some]
    ihave #Hj : decJust γ cf σ.t (.obj (objId o)) $$ []
    · unfold decJust
      iexists propFacts σ.t (propPairs (tally ents0 0))
      iframe HF0
      ipureintro
      intro M _ _ hS
      exact decEv_props hS0 (propFacts_mem hS) (by rw [hsnd, ← hkk]; exact hge)
    ihave #Hdo : decObjOk γ cf σ.t (.obj (objId o)) o $$ []
    · unfold decObjOk
      isplitr
      · ipureintro; exact ⟨rfl, hos⟩
      · iexact Hoo
    imod frame_dec_commit γ k hk γl γc ch c σ x hmd (.obj (objId o)) $$ [Hsh Hcfg Hfr Hlc1 Hj] with
      ⟨Hfr, #Hmy, #Hdec⟩
    · iframe Hsh Hcfg Hfr Hlc1 Hj
    wp_apply (wp_toNet_dec γ k γl γc ch c { σ with Ke := FKey.mydec k σ.t :: σ.Ke }
      { x with cur := FKey.mydec k σ.t :: x.cur } w o (.obj (objId o)) hos
      (by unfold lenLedger; exact ht)) $$ [$Hpk $Hfr $Hw $Hdec $Hdo]
      as ⟨%L2, %sent2, Hfr⟩
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
      (slotPriv_fields e.loc _).1 $$ Hpriv
    try wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    try wp_auto
    ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
    · iframe; iexact Hmr2
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    wp_apply_core wp_propMajV_frozen D.majV γ k γl γc σ.t e he ents0 h0 hne $$ Hpl Hse Hsi Hlb
    rw [hhead]
    simp only [Option.map_some, Option.get!_some]
    iintro %v #Hv
    wp_auto
    ihave Hrun := exRun_join γ k γl γc ch c
      ({ ({ σ with Ke := FKey.mydec k σ.t :: σ.Ke } : ExSt) with L := L2, sent := sent2 })
      ({ x with cur := FKey.mydec k σ.t :: x.cur }) e
      ({ x.pv with phase := x.pv.phase, round := x.pv.round + W32 1 })
      he hmy $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    iapply HΦ
    iexists (W32 0)
    unfold afterPost
    simp only [↓reduceIte]
    iexists _, _, (DVal.obj (objId o)), o
    iframe Hrun
    isplitr
    · ipureintro
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp⟩
    unfold decidedW
    iframe Hmy Hdec Hdo Hv
  · rw [decide_eq_false (by word)]
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    wp_apply_core wp_propMajT_frozen D.majT γ k γl γc σ.t e he ents0 h0 hne $$ Hpl Hse Hsi Hlb
    rw [hhead]
    simp only [Option.map_some, Option.getD_some]
    let B : Nat := if kk ≥ cf.maj then 1 else 2
    ihave #Hjust : nextJust γ k σ.t ((x.pv.setMy 0 2 (W32 B)) |> fun p => { p with round := 2 })
      $$ []
    · unfold nextJust
      rw [if_neg (by simp), if_pos rfl]
      unfold factJust
      iexists cfgFact cf :: propFacts σ.t (propPairs (tally ents0 0))
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe Hcff HF0
      · ipureintro
        simp only []
        have h00 : ((0 : w32)).toNat = 0 := rfl
        rw [PrivSt.my_with, PrivSt.setMy_phase, hp0, h00, PrivSt.my_setMy _ _ _ _ (Or.inr rfl)]
        have hBn : (W32 B).toNat = B := by simp only [B]; split <;> rfl
        rw [hBn]
        by_cases hm : kk ≥ cf.maj
        · have hB1 : B = 1 := by simp only [B]; rw [if_pos hm]
          rw [hB1]
          exact vote0_one_valid hk hS0 (id := objId o) (by rw [hsnd, ← hkk]; exact hm)
        · have hB2 : B = 2 := by simp only [B]; rw [if_neg hm]
          rw [hB2]
          exact vote0_q_valid hk hS0 hl0 (fun id => by have := hcnt id; omega)
    wp_auto
    by_cases hm : kk ≥ cf.maj
    · have hBv : B = 1 := by simp only [B]; rw [if_pos hm]
      rw [decide_eq_true (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (W32 0) (W32 2) (W32 1) (Or.inr rfl) $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy 0 2 (W32 B)) $$ [Hpriv]
      · rw [hBv]; iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      try wp_auto
      have hr2 : x.pv.round + W32 1 = (2 : w32) := by rw [hr1]; rfl
      ihave Hpriv := Hcl $$ %_ %(2 : w32) %mv2 [HPh HRd HMp Hrest]
      · rw [← hr2]; iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := ((x.pv.setMy 0 2 (W32 B)) |> fun p => { p with round := 2 }) }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ((x.pv.setMy 0 2 (W32 B)) |> fun p => { p with round := 2 }) he (by
            rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
      iexact Hjust
    · have hBv : B = 2 := by simp only [B]; rw [if_neg hm]
      rw [decide_eq_false (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (W32 0) (W32 2) (W32 2) (Or.inr rfl) $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy 0 2 (W32 B)) $$ [Hpriv]
      · rw [hBv]; iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      try wp_auto
      have hr2 : x.pv.round + W32 1 = (2 : w32) := by rw [hr1]; rfl
      ihave Hpriv := Hcl $$ %_ %(2 : w32) %mv2 [HPh HRd HMp Hrest]
      · rw [← hr2]; iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := ((x.pv.setMy 0 2 (W32 B)) |> fun p => { p with round := 2 }) }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ((x.pv.setMy 0 2 (W32 B)) |> fun p => { p with round := 2 }) he (by
            rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, Or.inl rfl⟩
      iexact Hjust

theorem wp_phase0Round2AfterWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hRPW : rpwSpec (GF := GF) γ cf k γl γc ch c)
    (hGD : gdSpec (GF := GF) γ cf c)
    (σ : ExSt) (x : ExSlot) (hph : x.pv.phase = 0)
    (hx : x.pv.round = 2 ∧ x.ρs = exRound x.pv + 1) (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phase0Round2AfterWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 bit with
              phase := x.pv.phase + 1, round := 1 }) v b }} := by
  wp_start as ⟨#Hpre, Hrun⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨#Hcff, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hcb := cf_bounds hcf
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  obtain ⟨hr2, hρs⟩ := hx
  have hρ : exRound x.pv = 2 * (W32 0 : w32).toNat + (W32 2).toNat - 1 := by
    unfold exRound; rw [hph, hr2]; rfl
  have hρ1 : exRound x.pv = 1 := by rw [hρ]; rfl
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c σ.t e he $$ Hro
  imod quorum_bits γ k γl γc σ.t e he x.ql (W32 0 : w32).toNat (W32 2).toNat (exRound x.pv) (Or.inr rfl)
    hρ hn $$ [Hsi Hql] with ⟨%ents0, #Hlb, ⟨%h0, %hS, %hlW⟩, #HF⟩
  · iframe Hsi Hql
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hts : (W32 σ.t).toNat = σ.t := by unfold lenLedger at ht; word
  have hs : (W32 σ.t).toNat < lenLedger := by rw [hts]; exact ht
  have hvl : (valsOf (tally ents0 (exRound x.pv))).length = cf.q := by
    simp only [valsOf, List.length_map]; exact h0
  have hT := majT_le_length (valsOf (tally ents0 (exRound x.pv)))
  rw [hvl] at hT
  wp_auto
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c (W32 σ.t) hs $$ [$Hconf $Hro]
  try wp_auto
  have hmod : W32 σ.t % W32 10000 = W32 σ.t := by unfold lenLedger at ht; word
  rw [hmod]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl ht
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he (W32 0) (W32 2) (Or.inr rfl)
    (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
  wp_auto
  by_cases hge : majT (valsOf (tally ents0 (exRound x.pv))) ≥ cf.fp1
  · -- decide
    rw [decide_eq_true (by word)]
    wp_auto
    ihave Hrun := exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    ihave #Hev := bitEv_of γ σ.t (W32 0 : w32).toNat (W32 2).toNat _ hS (Or.inr ⟨rfl, hge⟩) $$ HF
    wp_apply (wp_findReturnValue_strong D γ k γl γc ch c hRPW σ { x with pv := x.pv } (W32 0)
      (W32 2) (Or.inr rfl) (Or.inr rfl) (valsOf (tally ents0 (exRound x.pv))) hq) $$ [$Hrun]
      as %m ⟨%σ', %x', %d, %o, Hrun, %hst, #Hm, #Hdo, #Hj⟩
    · isplitr
      · iexact Hpre
      isplitr
      · unfold notified; iexists x.ql; iframe Hql; ipureintro
        rw [← hρ]; exact hn
      isplitr
      · unfold frozenVals; iexists ents0; iframe Hlb; ipureintro
        rw [← hρ]; exact ⟨rfl, h0⟩
      · iexact Hev
    obtain ⟨hstep, hpv, hcur, hρs'⟩ := hst
    wp_apply (lc := 1) (hGD σ.t m o) $$ [$Hpre $Hm] as %w #Hw
    ihave ⟨%e', %hee', Hpriv, #Hro', #Hql', Hfr⟩ := exRun_split γ k γl γc ch c σ' x' $$ Hrun
    obtain ⟨he', ht', hmy'⟩ := hee'
    rw [hstep.1] at he'
    rw [he] at he'
    cases he'
    have hmd' : FKey.mydec k σ'.t ∉ x'.cur := by
      rw [hstep.1]
      rcases hcur with h | h <;> rw [h]
      · exact hmd
      · simp only [List.mem_cons, reduceCtorEq, _root_.false_or]; exact hmd
    imod frame_dec_commit γ k hk γl γc ch c σ' x' hmd' d $$ [Hsh Hcfg Hfr Hlc1 Hj] with
      ⟨Hfr, #Hmy, #Hdec⟩
    · iframe Hsh Hcfg Hfr Hlc1; rw [hstep.1]; iexact Hj
    ihave %hos := decObjOk_svrSeq γ σ.t d o $$ Hdo
    ihave #Hw' : msgRep w (decMsg o σ'.t) $$ [Hw]
    · rw [hstep.1]; iexact Hw
    ihave #Hdo' : decObjOk γ cf σ'.t d o $$ [Hdo]
    · rw [hstep.1]; iexact Hdo
    wp_apply (wp_toNet_dec γ k γl γc ch c { σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke }
      { x' with cur := FKey.mydec k σ'.t :: x'.cur } w o d (by rw [hstep.1]; exact hos)
      (by rw [hstep.1]; unfold lenLedger; exact ht)) $$ [$Hpk $Hfr $Hw' $Hdec $Hdo']
      as ⟨%L2, %sent2, Hfr⟩
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
      (slotPriv_fields e.loc _).1 $$ Hpriv
    try wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    try wp_auto
    ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
    · iframe; iexact Hmr2
    ihave Hrun := exRun_join γ k γl γc ch c
      ({ ({ σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke } : ExSt) with L := L2, sent := sent2 })
      ({ x' with cur := FKey.mydec k σ'.t :: x'.cur }) e
      ({ x'.pv with phase := x'.pv.phase, round := x'.pv.round + W32 1 })
      (by rw [hstep.1]; exact he) hmy' $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    iapply HΦ
    iexists (W32 0)
    unfold afterPost
    simp only [↓reduceIte]
    iexists _, _, d, o
    iframe Hrun
    isplitr
    · ipureintro
      exact ⟨⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2⟩,
        by simp [hstep.1]⟩
    unfold decidedW
    rw [← hstep.1]
    iframe Hmy Hdec Hdo'
    rw [hstep.1]
    iexact Hm
  · rw [decide_eq_false (by word)]
    wp_auto
    let B : Nat := if majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1 then
      majV (valsOf (tally ents0 (exRound x.pv))) else 0
    ihave #Hjust : nextJust γ k σ.t ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 }) $$ []
    · unfold nextJust
      rw [if_pos ⟨rfl, by show x.pv.phase + 1 ≠ 0; rw [hph]; decide⟩]
      unfold factJust
      iexists cfgFact cf :: bitFacts σ.t (W32 0 : w32).toNat (W32 2).toNat (bitPairs (tally ents0 (exRound x.pv)))
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe Hcff HF
      · ipureintro
        rw [PrivSt.my_with, hph, show ((0 : w32) + 1).toNat = 0 + 1 from rfl,
          show (0 : w32).toNat = 0 from rfl, PrivSt.my_setMy _ _ _ _ (Or.inl rfl)]
        have hBn : (W32 B).toNat = B := by
          simp only [B]; split
          · have := majV_le1 (valsOf (tally ents0 (exRound x.pv))); word
          · rfl
        rw [hBn]
        have hBs : if majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1 then
            B = majV (valsOf (tally ents0 (exRound x.pv))) else (if 0 = 0 then B = 0 else B ≤ 1) := by
          simp only [B]; split <;> simp_all
        exact state_valid (s := σ.t) (p := 0) hk hS hlW
          (by rw [bitPairs_snd]; exact Nat.lt_of_not_le hge) (by rw [bitPairs_snd]; exact hBs)
    by_cases hge1 : majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1
    · have hBv : B = majV (valsOf (tally ents0 (exRound x.pv))) := by
        show (if _ then _ else _) = _; rw [if_pos hge1]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he (W32 0) (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      wp_auto
      rw [decide_eq_true (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajV_frozen D.bcMajV γ k γl γc σ.t e he (W32 0) (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (W32 1) (W32 1) (W32 (majV (valsOf (tally ents0 (exRound x.pv))))) (Or.inl rfl) $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B)) $$ [Hpriv]
      · have h1 : x.pv.phase.toNat + 1 = 1 := by rw [hph]; rfl
        rw [h1, hBv]; try simp only [Nat.cast_zero]
        iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.incr e.loc _ $$ [$Hpl $Hpriv] as Hpriv
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      try wp_auto
      rw [show x.pv.round - 1 = W32 1 by rw [hr2]; rfl]
      wp_auto
      ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
      · iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with phase := x.pv.phase + 1, round := 1 })
          he (by rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        dsimp only
        simp only [PrivSt.setMy, show (W32 1 : w32) = 1 from rfl, if_true]
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
          by first | exact Or.inl rfl | exact Or.inr hwrapN | (right; bv_omega)⟩
      iexact Hjust
    · have hBv : B = 0 := by
        show (if _ then _ else _) = _; rw [if_neg hge1]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he (W32 0) (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      wp_auto
      rw [decide_eq_false (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (W32 1) (W32 1) (W32 0) (Or.inl rfl) $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B)) $$ [Hpriv]
      · have h1 : x.pv.phase.toNat + 1 = 1 := by rw [hph]; rfl
        rw [h1, hBv]; try simp only [Nat.cast_zero]
        iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.incr e.loc _ $$ [$Hpl $Hpriv] as Hpriv
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
        (slotPriv_fields e.loc _).1 $$ Hpriv
      try wp_auto
      rw [show x.pv.round - 1 = W32 1 by rw [hr2]; rfl]
      wp_auto
      ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
      · iframe; iexact Hmr2
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with phase := x.pv.phase + 1, round := 1 })
          he (by rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        dsimp only
        simp only [PrivSt.setMy, show (W32 1 : w32) = 1 from rfl, if_true]
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
          by first | exact Or.inl rfl | exact Or.inr hwrapN | (right; bv_omega)⟩
      iexact Hjust

theorem wp_phaseNRound2AfterWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hRPW : rpwSpec (GF := GF) γ cf k γl γc ch c)
    (hGD : gdSpec (GF := GF) γ cf c)
    (σ : ExSt) (x : ExSlot) (hph : x.pv.phase ≠ 0)
    (hx : x.pv.round = 2 ∧ x.ρs = exRound x.pv + 1) (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phaseNRound2AfterWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 bit with
              phase := x.pv.phase + 1, round := 1 }) v b }} := by
  wp_start as ⟨#Hpre, Hrun⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨#Hcff, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hcb := cf_bounds hcf
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  obtain ⟨hr2, hρs⟩ := hx
  have hρ : exRound x.pv = 2 * x.pv.phase.toNat + (W32 2).toNat - 1 := by
    unfold exRound; rw [hr2]; rfl
  have hρ1 : exRound x.pv = 2 * x.pv.phase.toNat + 1 := by rw [hρ]; rfl
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c σ.t e he $$ Hro
  imod quorum_bits γ k γl γc σ.t e he x.ql x.pv.phase.toNat (W32 2).toNat (exRound x.pv) (Or.inr rfl)
    hρ hn $$ [Hsi Hql] with ⟨%ents0, #Hlb, ⟨%h0, %hS, %hlW⟩, #HF⟩
  · iframe Hsi Hql
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hts : (W32 σ.t).toNat = σ.t := by unfold lenLedger at ht; word
  have hs : (W32 σ.t).toNat < lenLedger := by rw [hts]; exact ht
  have hvl : (valsOf (tally ents0 (exRound x.pv))).length = cf.q := by
    simp only [valsOf, List.length_map]; exact h0
  have hT := majT_le_length (valsOf (tally ents0 (exRound x.pv)))
  rw [hvl] at hT
  wp_auto
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c (W32 σ.t) hs $$ [$Hconf $Hro]
  try wp_auto
  have hmod : W32 σ.t % W32 10000 = W32 σ.t := by unfold lenLedger at ht; word
  rw [hmod]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl ht
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  ihave ⟨HPh0, HRd0, ⟨%mv0, HMp0, #Hmr0⟩, %rest0, Hrest0, Hcl0⟩ :=
    (slotPriv_fields e.loc x.pv).1 $$ Hpriv
  wp_auto
  ihave Hpriv := Hcl0 $$ %x.pv.phase %x.pv.round %mv0 [HPh0 HRd0 HMp0 Hrest0]
  · iframe; iexact Hmr0
  ihave ⟨Hcoin, Hcoinb⟩ := frame_coin γ k γl γc ch c σ x $$ Hfr
  wp_apply wp_CommonCoinFlip c $$ [$Hpk $Hcoin] as %rb ⟨Hcoin, %hrb⟩
  ihave Hfr := Hcoinb $$ Hcoin
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he x.pv.phase (W32 2) (Or.inr rfl)
    (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
  wp_auto
  by_cases hge : majT (valsOf (tally ents0 (exRound x.pv))) ≥ cf.fp1
  · -- decide
    rw [decide_eq_true (by word)]
    wp_auto
    ihave Hrun := exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    ihave #Hev := bitEv_of γ σ.t x.pv.phase.toNat (W32 2).toNat _ hS (Or.inr ⟨rfl, hge⟩) $$ HF
    wp_apply (wp_findReturnValue_strong D γ k γl γc ch c hRPW σ { x with pv := x.pv } x.pv.phase
      (W32 2) (Or.inr rfl) (Or.inr rfl) (valsOf (tally ents0 (exRound x.pv))) hq) $$ [$Hrun]
      as %m ⟨%σ', %x', %d, %o, Hrun, %hst, #Hm, #Hdo, #Hj⟩
    · isplitr
      · iexact Hpre
      isplitr
      · unfold notified; iexists x.ql; iframe Hql; ipureintro
        rw [← hρ]; exact hn
      isplitr
      · unfold frozenVals; iexists ents0; iframe Hlb; ipureintro
        rw [← hρ]; exact ⟨rfl, h0⟩
      · iexact Hev
    obtain ⟨hstep, hpv, hcur, hρs'⟩ := hst
    wp_apply (lc := 1) (hGD σ.t m o) $$ [$Hpre $Hm] as %w #Hw
    ihave ⟨%e', %hee', Hpriv, #Hro', #Hql', Hfr⟩ := exRun_split γ k γl γc ch c σ' x' $$ Hrun
    obtain ⟨he', ht', hmy'⟩ := hee'
    rw [hstep.1] at he'
    rw [he] at he'
    cases he'
    have hmd' : FKey.mydec k σ'.t ∉ x'.cur := by
      rw [hstep.1]
      rcases hcur with h | h <;> rw [h]
      · exact hmd
      · simp only [List.mem_cons, reduceCtorEq, _root_.false_or]; exact hmd
    imod frame_dec_commit γ k hk γl γc ch c σ' x' hmd' d $$ [Hsh Hcfg Hfr Hlc1 Hj] with
      ⟨Hfr, #Hmy, #Hdec⟩
    · iframe Hsh Hcfg Hfr Hlc1; rw [hstep.1]; iexact Hj
    ihave %hos := decObjOk_svrSeq γ σ.t d o $$ Hdo
    ihave #Hw' : msgRep w (decMsg o σ'.t) $$ [Hw]
    · rw [hstep.1]; iexact Hw
    ihave #Hdo' : decObjOk γ cf σ'.t d o $$ [Hdo]
    · rw [hstep.1]; iexact Hdo
    wp_apply (wp_toNet_dec γ k γl γc ch c { σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke }
      { x' with cur := FKey.mydec k σ'.t :: x'.cur } w o d (by rw [hstep.1]; exact hos)
      (by rw [hstep.1]; unfold lenLedger; exact ht)) $$ [$Hpk $Hfr $Hw' $Hdec $Hdo']
      as ⟨%L2, %sent2, Hfr⟩
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    ihave ⟨HPh, HRd, ⟨%mv2, HMp, #Hmr2⟩, %rest2, Hrest, Hcl⟩ :=
      (slotPriv_fields e.loc _).1 $$ Hpriv
    try wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    try wp_auto
    ihave Hpriv := Hcl $$ %_ %_ %mv2 [HPh HRd HMp Hrest]
    · iframe; iexact Hmr2
    ihave Hrun := exRun_join γ k γl γc ch c
      ({ ({ σ' with Ke := FKey.mydec k σ'.t :: σ'.Ke } : ExSt) with L := L2, sent := sent2 })
      ({ x' with cur := FKey.mydec k σ'.t :: x'.cur }) e
      ({ x'.pv with phase := x'.pv.phase, round := x'.pv.round + W32 1 })
      (by rw [hstep.1]; exact he) hmy' $$ [Hfr Hpriv]
    · iframe Hfr; iexact Hpriv
    iapply HΦ
    iexists (W32 0)
    unfold afterPost
    simp only [↓reduceIte]
    iexists _, _, d, o
    iframe Hrun
    isplitr
    · ipureintro
      exact ⟨⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2.1, hstep.2.2.2.2.2⟩,
        by simp [hstep.1]⟩
    unfold decidedW
    rw [← hstep.1]
    iframe Hmy Hdec Hdo'
    rw [hstep.1]
    iexact Hm
  · rw [decide_eq_false (by word)]
    wp_auto
    by_cases hwrap : x.pv.phase + 1 = 0
    · -- N9: at the phase wrap the executor blocks on `Done` (never closed, nothing sent)
      rw [show decide (x.pv.phase + W32 1 = W32 0) = true from decide_eq_true hwrap]
      ihave ⟨#HDf, #HDb⟩ := consRO_done γ k γl γc ch c $$ Hro
      wp_auto
      wp_apply (wp_bag_receive (V := Unit) γl.done ch.done doneP) $$ [$HDb] as %u Hf
      unfold doneP; iexfalso; iexact Hf
    rw [show decide (x.pv.phase + W32 1 = W32 0) = false from decide_eq_false hwrap]
    wp_auto
    have hwrapN : (x.pv.phase + 1).toNat = x.pv.phase.toNat + 1 := by bv_omega
    have hp0 : x.pv.phase.toNat ≠ 0 := fun h => hph (by bv_omega)
    let B : Nat := if majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1 then
      majV (valsOf (tally ents0 (exRound x.pv))) else rb.toNat
    ihave #Hjust : nextJust γ k σ.t ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 }) $$ []
    · unfold nextJust
      rw [if_pos ⟨rfl, by show x.pv.phase + 1 ≠ 0; exact hwrap⟩]
      unfold factJust
      iexists cfgFact cf :: bitFacts σ.t x.pv.phase.toNat (W32 2).toNat (bitPairs (tally ents0 (exRound x.pv)))
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe Hcff HF
      · ipureintro
        rw [PrivSt.my_with, hwrapN, PrivSt.my_setMy _ _ _ _ (Or.inl rfl)]
        have hBn : (W32 B).toNat = B := by
          simp only [B]; split
          · have := majV_le1 (valsOf (tally ents0 (exRound x.pv))); word
          · word
        rw [hBn]
        have hBs : if majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1 then
            B = majV (valsOf (tally ents0 (exRound x.pv)))
            else (if x.pv.phase.toNat = 0 then B = 0 else B ≤ 1) := by
          simp only [B]; split
          · rfl
          · (try rw [if_neg hp0]); omega
        exact state_valid (s := σ.t) (p := x.pv.phase.toNat) hk hS hlW
          (by rw [bitPairs_snd]; exact Nat.lt_of_not_le hge) (by rw [bitPairs_snd]; exact hBs)
    by_cases hge1 : majT (valsOf (tally ents0 (exRound x.pv))) ≥ 1
    · have hBv : B = majV (valsOf (tally ents0 (exRound x.pv))) := by
        show (if _ then _ else _) = _; rw [if_pos hge1]
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he x.pv.phase (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      wp_auto
      rw [decide_eq_true (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajV_frozen D.bcMajV γ k γl γc σ.t e he x.pv.phase (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (x.pv.phase + W32 1) (W32 1) (W32 (majV (valsOf (tally ents0 (exRound x.pv))))) (Or.inl rfl)
        $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B)) $$ [Hpriv]
      · rw [show (W32 1 : w32) = 1 from rfl, ← hwrapN, hBv]
        iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.incr e.loc _ $$ [$Hpl $Hpriv] as Hpriv
      try wp_auto
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with phase := x.pv.phase + 1, round := 1 })
          he (by rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        dsimp only
        simp only [PrivSt.setMy, hr2, show (W32 1 : w32) = 1 from rfl, show (2 : w32) - 1 = 1 from rfl, if_true]
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
          by first | exact Or.inl rfl | exact Or.inr hwrapN | (right; bv_omega)⟩
      iexact Hjust
    · have hBv : B = rb.toNat := by
        show (if _ then _ else _) = _; rw [if_neg hge1]
      have hrbB : (W32 B : w32) = rb := by rw [hBv]; word
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_bcMajT_frozen D.bcMajT γ k γl γc σ.t e he x.pv.phase (W32 2) (Or.inr rfl)
        (Or.inr rfl) _ hρ ents0 h0 $$ Hpl Hse Hsi Hlb
      wp_auto
      rw [decide_eq_false (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.setMyBC e.loc x.pv (x.pv.phase + W32 1) (W32 1) (rb) (Or.inl rfl)
        $$ [$Hpl $Hpriv] as Hpriv
      ihave Hpriv : slotPriv e.loc (x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B)) $$ [Hpriv]
      · rw [show (W32 1 : w32) = 1 from rfl, ← hwrapN, hrbB]
        iexact Hpriv
      try wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply D.incr e.loc _ $$ [$Hpl $Hpriv] as Hpriv
      try wp_auto
      iapply HΦ
      iexists (W32 B)
      unfold afterPost
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ, { x with pv := { x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with
        phase := x.pv.phase + 1, round := 1 } }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 (W32 B) with phase := x.pv.phase + 1, round := 1 })
          he (by rw [← hmy]; rfl) $$ [Hfr Hpriv]
        iframe Hfr
        dsimp only
        simp only [PrivSt.setMy, hr2, show (W32 1 : w32) = 1 from rfl, show (2 : w32) - 1 = 1 from rfl, if_true]
        iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
          by first | exact Or.inl rfl | exact Or.inr hwrapN | (right; bv_omega)⟩
      iexact Hjust



/-- `wp_voteAfterWait` (ExecDefs), with the premises it misses: `k < cf.n`, `preq`/`mydec` of slot
`t` not yet written, and the callees' specs. -/
theorem wp_voteAfterWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hRPW : rpwSpec (GF := GF) γ cf k γl γc ch c) (hGD : gdSpec (GF := GF) γ cf c)
    (fn : GoString) (σ : ExSt) (x : ExSlot)
    (hfn : (fn = go!"phase0Round2AfterWait" ∧ x.pv.phase = 0) ∨
      (fn = go!"phaseNRound2AfterWait" ∧ x.pv.phase ≠ 0))
    (hx : x.pv.round = 2 ∧ x.ρs = exRound x.pv + 1) (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! fn)) (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 bit with
              phase := x.pv.phase + 1, round := 1 }) v b }} := by
  rcases hfn with ⟨rfl, hph⟩ | ⟨rfl, hph⟩
  · exact wp_phase0Round2AfterWait_proof D γ k γl γc ch c hk hRPW hGD σ x hph hx hn hq hmd
  · exact wp_phaseNRound2AfterWait_proof D γ k γl γc ch c hk hRPW hGD σ x hph hx hn hq hmd

/-- `wp_voteAfterWait` with `requestProposalAndWait` discharged. -/
theorem wp_voteAfterWait_proof' (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hGD : gdSpec (GF := GF) γ cf c)
    (fn : GoString) (σ : ExSt) (x : ExSlot)
    (hfn : (fn = go!"phase0Round2AfterWait" ∧ x.pv.phase = 0) ∨
      (fn = go!"phaseNRound2AfterWait" ∧ x.pv.phase ≠ 0))
    (hx : x.pv.round = 2 ∧ x.ρs = exRound x.pv + 1) (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! fn)) (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy (x.pv.phase.toNat + 1) 1 bit with
              phase := x.pv.phase + 1, round := 1 }) v b }} :=
  wp_voteAfterWait_proof D γ k γl γc ch c hk
    (fun σ x hq => wp_requestProposalAndWait_strong D γ k γl γc ch c hk σ x hq) hGD
    fn σ x hfn hx hn hq hmd

/-- `phaseNRound1AfterWait` with `requestProposalAndWait` discharged. -/
theorem wp_phaseNRound1AfterWait_proof' (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (hGD : gdSpec (GF := GF) γ cf c) (σ : ExSt) (x : ExSlot)
    (hx : x.pv.phase ≠ 0 ∧ x.pv.round = 1 ∧ x.ρs = exRound x.pv + 1)
    (hn : some (exRound x.pv) ∈ x.ql)
    (hq : FKey.preq k σ.t ∉ x.cur) (hmd : FKey.mydec k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"phaseNRound1AfterWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj) (b : Bool), RET (PairV #v #b);
        ∃ bit : w32, afterPost γ cf k γl γc ch c σ x
          ({ x.pv.setMy x.pv.phase.toNat 2 bit with round := 2 }) v b }} :=
  wp_phaseNRound1AfterWait_proof D γ k γl γc ch c hk
    (fun σ x hq => wp_requestProposalAndWait_strong D γ k γl γc ch c hk σ x hq) hGD σ x hx hn hq hmd

end after

end Perennial.rabia.roles.server.layers.consensus
