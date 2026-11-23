/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecDecide.lean`, run `rabia-r1wake-1`.)

`decideSlot(seq)`: the composition of the executor's rounds (phase 0's two rounds, then the phases'
loop), with the slot's written keys tracked (`CurOk`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecAfter
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecEpilogue

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- The keys written at slot `t` before round `ρs`: the proposal, the states and votes below. -/
def CurOk (k t : Nat) (cur : List FKey) (ρs : Nat) : Prop :=
  ∀ key ∈ cur, key = .prop k t ∨ (∃ p, key = .st k t p ∧ 2 * p < ρs) ∨
    (∃ p, key = .vt k t p ∧ 2 * p + 1 < ρs)

theorem CurOk.binKey_not {k t : Nat} {cur : List FKey} {pv : PrivSt}
    (h : CurOk k t cur (exRound pv)) (hr : pv.round = 1 ∨ pv.round = 2) :
    binKey k t pv ∉ cur := by
  intro hm
  rcases h _ hm with e | ⟨p, e, hp⟩ | ⟨p, e, hp⟩ <;> unfold binKey at e <;> split at e <;>
    simp at e <;> unfold exRound at hp <;> rcases hr with hr | hr <;> simp_all <;> omega

theorem CurOk.preq_not {k t : Nat} {cur : List FKey} {ρs : Nat} (h : CurOk k t cur ρs) :
    FKey.preq k t ∉ cur := by
  intro hm; rcases h _ hm with e | ⟨p, e, _⟩ | ⟨p, e, _⟩ <;> simp at e

theorem CurOk.mydec_not {k t : Nat} {cur : List FKey} {ρs : Nat} (h : CurOk k t cur ρs) :
    FKey.mydec k t ∉ cur := by
  intro hm; rcases h _ hm with e | ⟨p, e, _⟩ | ⟨p, e, _⟩ <;> simp at e

theorem CurOk.cons_bin {k t : Nat} {cur : List FKey} {pv : PrivSt}
    (h : CurOk k t cur (exRound pv)) (hr : pv.round = 1 ∨ pv.round = 2) :
    CurOk k t (binKey k t pv :: cur) (exRound pv + 1) := by
  intro key hm
  rcases List.mem_cons.1 hm with e | hm
  · subst e; unfold binKey exRound; split
    · rename_i h1; right; left; refine ⟨_, rfl, ?_⟩; simp [h1]
    · right; right; refine ⟨_, rfl, ?_⟩; rcases hr with hr | hr <;> simp_all <;> omega
  · rcases h _ hm with e | ⟨p, e, hp⟩ | ⟨p, e, hp⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨p, e, by omega⟩)
    · exact Or.inr (Or.inr ⟨p, e, by omega⟩)

theorem CurOk.mono {k t : Nat} {cur : List FKey} {a b : Nat} (h : CurOk k t cur a) (hab : a ≤ b) :
    CurOk k t cur b := by
  intro key hm
  rcases h _ hm with e | ⟨p, e, hp⟩ | ⟨p, e, hp⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨p, e, by omega⟩)
  · exact Or.inr (Or.inr ⟨p, e, by omega⟩)

@[simp] theorem setMy_phase (pv : PrivSt) (p r : Nat) (x : w32) : (pv.setMy p r x).phase = pv.phase := rfl

theorem setMy_len (pv : PrivSt) (p r : Nat) (x : w32) : p < (pv.setMy p r x).myBC.length := by
  unfold PrivSt.setMy; simp; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS] [math.rand.Hyps GF]

theorem exRun_ql (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) :
    exRun (GF := GF) γ cf k γl γc ch c σ x ⊢ exRun γ cf k γl γc ch c σ x ∗
      ⌜x.ql.filterMap id = List.range (x.ql.filterMap id).length ∧ σ.t < lenLedger⌝ := by
  unfold exRun exSlotRes
  iintro ⟨Hc, Hco, Hs, %ht, %e, %he, Hp, %hm, Hpo, Hcn, #Hq, %hq, Hx⟩
  isplitl [Hc Hco Hs Hp Hpo Hcn Hx]
  · iframe Hc Hco Hs
    isplitr
    · ipureintro; exact ht
    iexists e
    iframe Hp Hpo Hcn Hq Hx
    ipureintro; exact ⟨he, hm, hq⟩
  · ipureintro; exact ⟨hq.2.1, ht⟩

theorem some_mem_of_range {ql : List (Option Nat)} {ρ : Nat}
    (h : ql.filterMap id = List.range (ql.filterMap id).length)
    (hl : ρ < (ql.filterMap id).length) : some ρ ∈ ql := by
  have : ρ ∈ ql.filterMap id := by rw [h]; simpa using hl
  simpa using this

/-- `decideSlot`'s phases loop: at a phase `≥ 1`'s round 1, its state to send justified. -/
def loopI (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (t : Nat) (o : ObjV) : IProp GF :=
  iprop(∃ σ' x', exRun γ cf k γl γc ch c σ' x' ∗ nextJust γ k t x'.pv ∗
    ⌜σ'.t = t ∧ x'.o = o ∧ x'.pv.round = 1 ∧ x'.pv.phase ≠ 0 ∧ x'.ρs = exRound x'.pv ∧
      (x'.ql.filterMap id).length = exRound x'.pv ∧ none ∉ x'.ql ∧
      x'.pv.phase.toNat < x'.pv.myBC.length ∧ CurOk k t x'.cur x'.ρs⌝)

theorem wp_decideSlot_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames)
    (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n) (σ : ExSt) (x : ExSlot)
    (hx : x.pv.phase = 0 ∧ x.pv.round = 1 ∧ x.pv.myBC = [] ∧ x.recv = [] ∧ x.ql = [] ∧
      x.ρs = 0 ∧ x.cur = []) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"decideSlot")) (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ', exIdle γ cf k γl γc ch c σ' ∗ ⌜σ'.t = σ.t + 1⌝ }} := by
  obtain ⟨hph, hrd, hbc, hrecv, hql, hρ, hcur⟩ := hx
  wp_start as ⟨#Hpre, Hrun⟩
  wp_auto
  wp_apply (wp_phase0Round1BeforeWait_proof (cf := cf) D γ k γl γc ch c hk σ x ⟨hph, hrd, hρ, hcur⟩)
    $$ [$Hpre $Hrun] as ⟨%σ1, %x1, Hrun, %h1, #Hprop⟩
  obtain ⟨⟨ht1, hH1, hc1, ho1, hr1, hq1⟩, hpv1, hρ1, hcur1⟩ := h1
  have hEpi := fun σ x d o v hd => wp_epilogue_proof (cf := cf) D γ k γl γc ch c σ x d o v hd
  have hGD := fun s v o => wp_genDecMsgType2_proof (cf := cf) (D := D) (γ := γ) (c := c) s v o
  have hw := wp_wait_proof (cf := cf) D γ k γl γc ch c hk hEpi σ1 x1 (by rw [hpv1, hrd]; simp)
    (by rw [hρ1, hpv1]; simp [exRound, hph, hrd]) (by rw [hq1, hql]; simp [exRound, hpv1, hph, hrd])
    (by rw [hq1, hql]; simp)
  rw [ht1] at hw
  wp_apply hw $$ [$Hpre $Hrun] as %b Hb
  · rw [ho1]; iexact Hprop
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; iexact Hb
  simp only [↓reduceIte]
  icases Hb with ⟨%x2, Hrun, %h2⟩
  obtain ⟨hpv2, hρ2, hcur2, ho2, hn2, hnone2⟩ := h2
  ihave ⟨Hrun, %hr2⟩ := exRun_ql γ k γl γc ch c σ1 x2 $$ Hrun
  wp_auto
  have hA1 := wp_phase0Round1AfterWait_proof D γ k γl γc ch c hk σ1 x2
    ⟨by rw [hpv2, hpv1, hph], by rw [hpv2, hpv1, hrd], by rw [hρ2, hρ1]⟩
    (some_mem_of_range hr2.1 (by rw [hn2]; simp [exRound, hpv1, hph, hrd]))
    (by rw [hcur2, hcur1]; simp)
  rw [ht1] at hA1
  wp_apply hA1 $$ [$Hpre $Hrun] as %v %b ⟨%bit, Hap⟩
  unfold afterPost
  cases b
  rotate_left
  · simp only [↓reduceIte]
    icases Hap with ⟨%σ', %x', %d, %o, Hrun, %hst, Hdw⟩
    obtain ⟨⟨ht', -, -, ho', -, -⟩, hmy'⟩ := hst
    wp_auto
    have hE := wp_epilogue_proof (cf := cf) D γ k γl γc ch c σ' x' d o v (by rw [ht']; exact hmy')
    rw [ht', ht1] at hE
    wp_apply hE $$ [$Hpre $Hrun Hdw] as ⟨%σ'', Hidle, %ht''⟩
    · isplitl [Hdw]
      · rw [← ht1]; iexact Hdw
      · rw [ho', ho2, ho1]; iexact Hprop
    iapply HΦ
    iexists σ''; iframe Hidle; ipureintro; exact ht''
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hap with ⟨%σ3, %x3, Hrun, %h3, #Hj3⟩
  obtain ⟨⟨ht3, -, -, ho3, -, hq3⟩, hpv3, hρ3, hcur3, -⟩ := h3
  wp_auto
  have hx3ph : x3.pv.phase = 0 := by rw [hpv3]; simp [PrivSt.setMy, hpv2, hpv1, hph]
  have hx3rd : x3.pv.round = 2 := by rw [hpv3]
  have hx3ρ : x3.ρs = exRound x3.pv := by
    rw [hρ3, hρ2, hρ1]; simp [exRound, hx3ph, hx3rd]
  have hcur3' : CurOk k σ3.t x3.cur (exRound x3.pv) := by
    rw [hcur3, hcur2, hcur1, ht3, ht1]; intro key hm; simp at hm; exact Or.inl hm
  have hB2 := wp_phase0Round2BeforeWait_proof (cf := cf) D γ k γl γc ch c σ3 x3 hx3ph hx3rd hx3ρ
    (by have h := setMy_len x2.pv 0 2 bit; have h0 := hx3ph; rw [hpv3] at h0 ⊢; simp only at h0 ⊢; rw [h0]; simpa using h)
    (hcur3'.binKey_not (Or.inr hx3rd))
  rw [ht3, ht1] at hB2
  wp_apply hB2 $$ [$Hpre $Hrun] as ⟨%σ4, %x4, Hrun, %h4⟩
  · rw [hpv3, ← ht1]; iexact Hj3
  obtain ⟨⟨ht4, -, -, ho4, -, hq4⟩, hpv4, hρ4, hcur4⟩ := h4
  have hw2 := wp_wait_proof (cf := cf) D γ k γl γc ch c hk hEpi σ4 x4 (by rw [hpv4, hx3rd]; simp)
    (by rw [hρ4, hpv4, hx3ρ]) (by rw [hq4, hq3, hn2, hpv4]; simp [exRound, hx3ph, hx3rd, hpv1, hph, hrd])
    (by rw [hq4, hq3]; exact hnone2)
  rw [ht4, ht3, ht1] at hw2
  wp_apply hw2 $$ [$Hpre $Hrun] as %b Hb
  · rw [ho4, ho3, ho2, ho1]; iexact Hprop
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ; iexact Hb
  simp only [↓reduceIte]
  icases Hb with ⟨%x5, Hrun, %h5⟩
  obtain ⟨hpv5, hρ5, hcur5, ho5, hn5, hnone5⟩ := h5
  ihave ⟨Hrun, %hr5⟩ := exRun_ql γ k γl γc ch c σ4 x5 $$ Hrun
  have hx5ph : x5.pv.phase = 0 := by rw [hpv5, hpv4]; exact hx3ph
  have hx5rd : x5.pv.round = 2 := by rw [hpv5, hpv4]; exact hx3rd
  have hcur5' : CurOk k σ4.t x5.cur x5.ρs := by
    have h := hcur3'.cons_bin (Or.inr hx3rd)
    rw [ht3, ht1, ← hx3ρ] at h
    rw [hcur5, hcur4, hρ5, hρ4, ht4, ht3, ht1]; exact h
  have hV0 := wp_voteAfterWait_proof' D γ k γl γc ch c hk hGD go!"phase0Round2AfterWait" σ4 x5
    (Or.inl ⟨rfl, hx5ph⟩) ⟨hx5rd, by rw [hρ5, hρ4, hpv5, hpv4, hx3ρ]⟩
    (some_mem_of_range hr5.1 (by rw [hn5, hpv5]; omega))
    hcur5'.preq_not hcur5'.mydec_not
  rw [ht4, ht3, ht1] at hV0
  wp_auto
  wp_apply hV0 $$ [$Hpre $Hrun] as %v %b ⟨%bit, Hap⟩
  unfold afterPost
  cases b
  rotate_left
  · simp only [↓reduceIte]
    icases Hap with ⟨%σ', %x', %d, %o, Hrun, %hst, Hdw⟩
    obtain ⟨⟨ht', -, -, ho', -, -⟩, hmy'⟩ := hst
    wp_auto
    have hE := wp_epilogue_proof (cf := cf) D γ k γl γc ch c σ' x' d o v (by rw [ht']; exact hmy')
    rw [ht', ht4, ht3, ht1] at hE
    wp_apply hE $$ [$Hpre $Hrun Hdw] as ⟨%σ'', Hidle, %ht''⟩
    · isplitl [Hdw]
      · have e4 : σ4.t = σ.t := by rw [ht4, ht3, ht1]
        rw [← e4]; iexact Hdw
      · rw [ho', ho5, ho4, ho3, ho2, ho1]; iexact Hprop
    iapply HΦ
    iexists σ''; iframe Hidle; ipureintro; exact ht''
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hap with ⟨%σ6, %x6, Hrun, %h6, #Hj6⟩
  obtain ⟨⟨ht6, -, -, ho6, -, hq6⟩, hpv6, hρ6, hcur6, -⟩ := h6
  ihave HI : loopI γ cf k γl γc ch c σ.t x.o $$ [Hrun]
  · unfold loopI; iexists σ6, x6
    iframe Hrun
    isplitr
    · have e4 : σ4.t = σ.t := by rw [ht4, ht3, ht1]
      rw [← e4, hpv6]; iexact Hj6
    ipureintro
    refine ⟨by rw [ht6, ht4, ht3, ht1], by rw [ho6, ho5, ho4, ho3, ho2, ho1], by rw [hpv6],
      by rw [hpv6]; simp [hx5ph], ?_, ?_, by rw [hq6]; exact hnone5, ?_, ?_⟩
    · rw [hpv6, hρ6, hρ5, hρ4, hx3ρ]; simp [exRound, hx5ph, hx3ph, hx3rd]
    · rw [hpv6, hq6, hn5, hpv4]; simp [exRound, hx5ph, hx3ph, hx3rd]
    · rw [hpv6]; simp only [hx5ph]
      have := setMy_len x5.pv (x5.pv.phase.toNat + 1) 1 bit
      simp [hx5ph] at this ⊢; omega
    · rw [hcur6, hρ6]; rw [ht4, ht3, ht1] at hcur5'; exact hcur5'
  wp_auto
  wp_for
  unfold loopI
  icases HI with ⟨%σa, %xa, Hrun, #Hja, %ha⟩
  obtain ⟨hta, hoa, hrda, hpha, hρa, hna, hnonea, hpa, hcura⟩ := ha
  have hBa := wp_phaseNRound1BeforeWait_proof (cf := cf) D γ k γl γc ch c σa xa hpha hrda hρa hpa
    (by rw [hta]; rw [hρa] at hcura; exact hcura.binKey_not (Or.inl hrda))
  rw [hta] at hBa
  wp_apply hBa $$ [$Hpre $Hrun] as ⟨%σb, %xb, Hrun, %hb⟩
  · iexact Hja
  obtain ⟨⟨htb, -, -, hob, -, hqb⟩, hpvb, hρb, hcurb⟩ := hb
  have hwb := wp_wait_proof (cf := cf) D γ k γl γc ch c hk hEpi σb xb (by rw [hpvb, hrda]; simp)
    (by rw [hρb, hpvb, hρa]) (by rw [hqb, hna, hpvb]) (by rw [hqb]; exact hnonea)
  rw [htb, hta] at hwb
  wp_apply hwb $$ [$Hpre $Hrun] as %b Hb
  · rw [hob, hoa]; iexact Hprop
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iapply HΦ; iexact Hb
  simp only [↓reduceIte]
  icases Hb with ⟨%xc, Hrun, %hc⟩
  obtain ⟨hpvc, hρc, hcurc, hoc, hnc, hnonec⟩ := hc
  ihave ⟨Hrun, %hrc⟩ := exRun_ql γ k γl γc ch c σb xc $$ Hrun
  wp_auto
  have hcurc' : CurOk k σb.t xc.cur (exRound xa.pv + 1) := by
    have hc0 : CurOk k σ.t xa.cur (exRound xa.pv) := by rw [← hρa]; exact hcura
    have h := hc0.cons_bin (Or.inl hrda)
    rw [hcurc, hcurb, htb, hta]; exact h
  have hA := wp_phaseNRound1AfterWait_proof' D γ k γl γc ch c hk hGD σb xc
    ⟨by rw [hpvc, hpvb]; exact hpha, by rw [hpvc, hpvb]; exact hrda,
      by rw [hρc, hρb, hpvc, hpvb, hρa]⟩
    (some_mem_of_range hrc.1 (by rw [hnc, hpvc]; omega))
    hcurc'.preq_not hcurc'.mydec_not
  rw [htb, hta] at hA
  wp_apply hA $$ [$Hpre $Hrun] as %v %b ⟨%bit, Hap⟩
  unfold afterPost
  cases b
  rotate_left
  · simp only [↓reduceIte]
    icases Hap with ⟨%σ', %x', %d, %o, Hrun, %hst, Hdw⟩
    obtain ⟨⟨ht', -, -, ho', -, -⟩, hmy'⟩ := hst
    wp_auto
    have hE := wp_epilogue_proof (cf := cf) D γ k γl γc ch c σ' x' d o v (by rw [ht']; exact hmy')
    rw [ht', htb, hta] at hE
    wp_apply hE $$ [$Hpre $Hrun Hdw] as ⟨%σ'', Hidle, %ht''⟩
    · isplitl [Hdw]
      · have eb : σb.t = σ.t := by rw [htb, hta]
        rw [← eb]; iexact Hdw
      · rw [ho', hoc, hob, hoa]; iexact Hprop
    wp_for_post
    iapply HΦ
    iexists σ''; iframe Hidle; ipureintro; exact ht''
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hap with ⟨%σd, %xd, Hrun, %hd, #Hjd⟩
  obtain ⟨⟨htd, -, -, hod, -, hqd⟩, hpvd, hρd, hcurd, -⟩ := hd
  wp_auto
  have hxdph : xd.pv.phase = xa.pv.phase := by rw [hpvd]; simp [PrivSt.setMy, hpvc, hpvb]
  have hxdrd : xd.pv.round = 2 := by rw [hpvd]
  have hxdρ : xd.ρs = exRound xd.pv := by
    rw [hρd, hρc, hρb, hρa]; simp [exRound, hxdph, hxdrd, hrda]
  have hcurd' : CurOk k σ.t xd.cur (exRound xd.pv) := by
    have hc0 : CurOk k σ.t xa.cur (exRound xa.pv) := by rw [← hρa]; exact hcura
    have h := hc0.cons_bin (Or.inl hrda)
    have e : exRound xd.pv = exRound xa.pv + 1 := by simp [exRound, hxdph, hxdrd, hrda]
    rw [hcurd, hcurc, hcurb, e]; exact h
  have hBd := wp_phaseNRound2BeforeWait_proof (cf := cf) D γ k γl γc ch c σd xd hxdrd hxdρ
    (by have h := setMy_len xc.pv xc.pv.phase.toNat 2 bit; have h0 := hxdph
        rw [hpvd] at h0 ⊢; simpa using h)
    (by rw [htd, htb, hta]; exact hcurd'.binKey_not (Or.inr hxdrd))
  rw [htd, htb, hta] at hBd
  wp_apply hBd $$ [$Hpre $Hrun] as ⟨%σe, %xe, Hrun, %he⟩
  · have eb : σb.t = σ.t := by rw [htb, hta]
    rw [hpvd, ← eb]; iexact Hjd
  obtain ⟨⟨hte, -, -, hoe, -, hqe⟩, hpve, hρe, hcure⟩ := he
  have hwe := wp_wait_proof (cf := cf) D γ k γl γc ch c hk hEpi σe xe (by rw [hpve, hxdrd]; simp)
    (by rw [hρe, hpve, hxdρ]) (by rw [hqe, hqd, hnc, hpve, hpvb]; simp [exRound, hxdph, hxdrd, hrda])
    (by rw [hqe, hqd]; exact hnonec)
  rw [hte, htd, htb, hta] at hwe
  wp_apply hwe $$ [$Hpre $Hrun] as %b Hb
  · rw [hoe, hod, hoc, hob, hoa]; iexact Hprop
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iapply HΦ; iexact Hb
  simp only [↓reduceIte]
  icases Hb with ⟨%xf, Hrun, %hf⟩
  obtain ⟨hpvf, hρf, hcurf, hof, hnf, hnonef⟩ := hf
  ihave ⟨Hrun, %hrf⟩ := exRun_ql γ k γl γc ch c σe xf $$ Hrun
  wp_auto
  have hxfph : xf.pv.phase ≠ 0 := by rw [hpvf, hpve, hxdph]; exact hpha
  have hxfrd : xf.pv.round = 2 := by rw [hpvf, hpve]; exact hxdrd
  have hcurf' : CurOk k σe.t xf.cur xf.ρs := by
    have h := hcurd'.cons_bin (Or.inr hxdrd)
    rw [hcurf, hcure, hρf, hρe, hxdρ, hte, htd, htb, hta]; exact h
  have hV := wp_voteAfterWait_proof' D γ k γl γc ch c hk hGD go!"phaseNRound2AfterWait" σe xf
    (Or.inr ⟨rfl, hxfph⟩) ⟨hxfrd, by rw [hρf, hρe, hpvf, hpve, hxdρ]⟩
    (some_mem_of_range hrf.1 (by rw [hnf, hpvf]; omega))
    hcurf'.preq_not hcurf'.mydec_not
  rw [hte, htd, htb, hta] at hV
  wp_apply hV $$ [$Hpre $Hrun] as %v %b ⟨%bit, Hap⟩
  unfold afterPost
  cases b
  rotate_left
  · simp only [↓reduceIte]
    icases Hap with ⟨%σ', %x', %d, %o, Hrun, %hst, Hdw⟩
    obtain ⟨⟨ht', -, -, ho', -, -⟩, hmy'⟩ := hst
    wp_auto
    have hE := wp_epilogue_proof (cf := cf) D γ k γl γc ch c σ' x' d o v (by rw [ht']; exact hmy')
    rw [ht', hte, htd, htb, hta] at hE
    wp_apply hE $$ [$Hpre $Hrun Hdw] as ⟨%σ'', Hidle, %ht''⟩
    · isplitl [Hdw]
      · have ee : σe.t = σ.t := by rw [hte, htd, htb, hta]
        rw [← ee]; iexact Hdw
      · rw [ho', hof, hoe, hod, hoc, hob, hoa]; iexact Hprop
    wp_for_post
    iapply HΦ
    iexists σ''; iframe Hidle; ipureintro; exact ht''
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hap with ⟨%σg, %xg, Hrun, %hg, #Hjg⟩
  obtain ⟨⟨htg, -, -, hog, -, hqg⟩, hpvg, hρg, hcurg, hphg⟩ := hg
  -- the next phase number does not wrap (N9: at the wrap the executor blocks on `Done`)
  have hnw : (xf.pv.phase + 1).toNat = xf.pv.phase.toNat + 1 := by
    rcases hphg with h | h
    · exfalso; have := congrArg BitVec.toNat h; simp at this; bv_omega
    · exact h
  wp_auto
  wp_for_post
  iframe
  simp only [named]
  iexists σg, xg
  iframe Hrun
  isplitr
  · have eg : σe.t = σ.t := by rw [hte, htd, htb, hta]
    rw [← eg, hpvg]; iexact Hjg
  ipureintro
  refine ⟨by rw [htg, hte, htd, htb, hta], by rw [hog, hof, hoe, hod, hoc, hob, hoa],
    by rw [hpvg], ?_, ?_, ?_, by rw [hqg]; exact hnonef, ?_, ?_⟩
  · rw [hpvg]; intro h0; have h1 := congrArg BitVec.toNat h0; simp only at h1; rw [hnw] at h1; simp at h1
  · rw [hpvg, hρg, hρf, hρe, hxdρ]; simp only [exRound] at hnw ⊢; rw [hnw]
    simp [hpvf, hpve, hxdrd, hxdph]; omega
  · rw [hpvg, hqg, hnf]; simp only [exRound] at hnw ⊢; rw [hnw]; simp [hpvf, hpve, hxdrd]; omega
  · rw [hpvg]; simp only
    have := setMy_len xf.pv (xf.pv.phase.toNat + 1) 1 bit
    rw [hnw]; simpa using this
  · rw [hcurg, hρg]; rw [hte, htd, htb, hta] at hcurf'; exact hcurf'


end proof

end Perennial.rabia.roles.server.layers.consensus
