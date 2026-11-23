/-
Lean-first (no Rocq counterpart). #33 S3b W3b (2026-11-23): the proof of `s.InMemory(n, ev)` (B 213-275,
`State.inMemory`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InMemory
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ok
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__role1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ld1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__ll2
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__lc1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__snapsM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__wins
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__cmt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__c
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__newC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setStr
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.ConfOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.LastConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InitConf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__snap
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__role
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__With
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Comparable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Set__Has
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.InMemoryLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem State.InMemory.wp_proof
    (wp_ok : inMem.ok.spec (GF := GF) (hG := hG))
    (wp_role1 : inMem.role1.spec (GF := GF) (hG := hG))
    (wp_ld1 : inMem.ld1.spec (GF := GF) (hG := hG))
    (wp_ll2 : inMem.ll2.spec (GF := GF) (hG := hG))
    (wp_lc1 : inMem.lc1.spec (GF := GF) (hG := hG))
    (wp_snapsM : inMem.snapsM.spec (GF := GF) (hG := hG))
    (wp_wins : inMem.wins.spec (GF := GF) (hG := hG))
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_cmt : inMem.cmt.spec (GF := GF) (hG := hG))
    (wp_c : inMem.c.spec (GF := GF) (hG := hG))
    (wp_newC : inMem.newC.spec (GF := GF) (hG := hG))
    (wp_setStr : setStr.spec (GF := GF) (hG := hG))
    (wp_setConf : setConf.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_ConfOf : ConfOf.spec (GF := GF) (hG := hG))
    (wp_LastConf : LastConf.spec (GF := GF) (hG := hG))
    (wp_InitConf : State.InitConf.spec (GF := GF) (hG := hG))
    (wp_snap : Event.snap.spec (GF := GF) (hG := hG))
    (wp_role : Event.role.spec (GF := GF) (hG := hG))
    (wp_With : TermInts.With.spec (GF := GF) (hG := hG))
    (wp_Comparable : Comparable.spec (GF := GF) (hG := hG))
    (wp_violAdd : violAdd.spec (GF := GF) (hG := hG))
    (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_Has : Set.Has.spec (GF := GF) (hG := hG)) :
    State.InMemory.spec (GF := GF) (hG := hG) := by
  intro p s n e ev r
  wp_start as ⟨#Hs, #He, %Hn, %Hlt, %HBd, %Ho⟩
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  ihave #Hx : inMemRO { s' := p, n' := n, ev' := e } { s, n := sint.nat n, ev } $$ []
  · iunfold inMemRO; iframe Hs He; ipureintro
    have := sint_nat_cast Hn
    exact ⟨this.symm, show sint.nat n < s.cfg.server.length by omega, HBd⟩
  obtain ⟨bb, EE, HW, HN, HC, hbb, hE⟩ := HBd
  unfold numBound Event.weight at hbb
  unfold State.inMemory at Ho
  replace Ho := bind_ok Ho; obtain ⟨ok, hok, Ho⟩ := Ho
  wp_auto
  iStructNamedPrefix r "R"
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ok_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ok _ _ ok $$ [Hx]
  · iframe Hx; ipureintro; exact hok
  have hnr : 0 ≤ sint.Z n ∧ sint.Z n < s.role.length := ⟨Hn, by rw [HWf.len_role]; exact Hlt⟩
  replace Ho := bind_ok Ho; obtain ⟨r1, hr1, Ho⟩ := Ho
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_role1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_role1 _ _ r1 $$ [Hx]
  · iframe Hx; ipureintro; exact hr1
  wp_apply wp_setStr _ _ n r1 $$ [HRole] as %grole #Hrole
  · iframe HRole; ipureintro; exact hnr
  replace Ho := bind_ok Ho; obtain ⟨ld, hld, Ho⟩ := Ho
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ld1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ld1 _ _ ld $$ [Hx] as %gld #Hld
  · iframe Hx; ipureintro; exact hld
  replace Ho := bind_ok Ho; obtain ⟨l2, hl2, Ho⟩ := Ho
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll2_unfold.method_unfold]
  try wp_auto
  wp_apply wp_ll2 _ _ l2 $$ [Hx] as %gl2 #Hl2
  · iframe Hx; ipureintro; exact hl2
  replace Ho := bind_ok Ho; obtain ⟨lc, hlc, Ho⟩ := Ho
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_lc1_unfold.method_unfold]
  try wp_auto
  wp_apply wp_lc1 _ _ lc $$ [Hx] as %glc #Hlc
  · iframe Hx; ipureintro; exact hlc
  extract_lets viol0 lc0 me vCS jp1 at Ho
  wp_join iprop(∃ (gcf gca : GoSlice) (cc : List Conf × List Int),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      r_ptr.[G.MemResult, go!"Config"] ↦ gcf ∗ r_ptr.[G.MemResult, go!"ConfAt"] ↦ gca ∗ confsRO gcf cc.1 ∗ intsRO gca cc.2 ∗ ⌜jp1 cc = .ok r⌝)
    at next with [x s ev n RConfig RConfAt] as ⟨%gcf, %gca, %cc, x, s, ev, n, RConfig, RConfAt, #Hcf, #Hca, %Hjp⟩
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_snapsM_unfold.method_unfold]
    try wp_auto
    wp_apply wp_snapsM _ _ $$ [Hx] as -
    · iexact Hx
    split at Ho
    · rename_i hsm
      simp only [hsm]
      wp_auto
      replace Ho := bind_ok Ho; obtain ⟨sn, hsn, Ho⟩ := Ho
      replace Ho := bind_ok Ho; obtain ⟨c, hc, Ho⟩ := Ho
      replace Ho := bind_ok Ho; obtain ⟨sn', hsn', Ho⟩ := Ho
      rw [hsn] at hsn'; cases hsn'
      replace Ho := bind_ok Ho; obtain ⟨a, ha, Ho⟩ := Ho
      replace Ho := bind_ok Ho; obtain ⟨cc, hcc, Ho⟩ := Ho
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      have hsnn : numOk sn.index ∧ numOk sn.term := HN.2.2.2.2.2.2.2.2.2.1 sn (need_ok hsn)
      unfold numOk numBound at hsnn
      wp_apply wp_snap e ev sn $$ [He] as %gsn %Hgsn
      · iframe He; ipureintro; exact hsn
      wp_apply wp_InitConf p s $$ [Hs] as %gic #Hic
      · iexact Hs
      wp_apply wp_ConfOf _ _ gsn.Index' _ _ c $$ [HChain Hic] as %gc #Hgc
      · iframe HChain Hic; ipureintro
        rw [Hgsn.1]
        exact ⟨hc, by omega, confOf_bounded_init HW hE⟩
      wp_apply wp_setConf _ _ n _ c $$ [HConfig Hgc] as %gcf #Hgcf
      · iframe HConfig Hgc; ipureintro; exact ⟨Hn, by rw [HWf.len_config]; exact Hlt⟩
      wp_apply wp_snap e ev sn $$ [He] as %gsn2 %Hgsn2
      · iframe He; ipureintro; exact hsn
      wp_apply wp_LastConf _ _ gsn2.Index' a $$ [HChain] as %ga %Hga
      · iframe HChain; ipureintro
        rw [Hgsn2.1]
        exact ⟨ha, by omega⟩
      wp_apply wp_setInt _ _ n ga $$ [HConfAt] as %gca #Hgca
      · iframe HConfAt; ipureintro; exact ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩
      wp_join_done
      iexists gcf, gca, (s.config.set (sint.nat n) c, s.confAt.set (sint.nat n) (sint.Z ga))
      iframe
      isplitr; · iexact Hgcf
      isplitr; · iexact Hgca
      ipureintro; rw [Hga]; exact Ho
    · rename_i hsm
      simp only [Bool.not_eq_true] at hsm
      simp only [hsm]
      wp_auto
      replace Ho := bind_ok Ho; obtain ⟨cc, hcc, Ho⟩ := Ho
      simp only [pure_ok, Except.ok.injEq] at hcc
      subst hcc
      wp_join_done
      iexists g.Config', g.ConfAt', (s.config, s.confAt)
      iframe
      isplitr; · iexact HConfig
      isplitr; · iexact HConfAt
      ipureintro; exact Ho
  clear Ho
  obtain ⟨config, confAt⟩ := cc
  simp -zeta only [jp1] at Hjp
  replace Hjp := bind_ok Hjp; obtain ⟨w, hw, Hjp⟩ := Hjp
  extract_lets jp2 at Hjp
  icases intsRO_at g.ConfAt' s.confAt n ⟨Hn, by rw [HWf.len_confAt]; exact Hlt⟩ $$ HConfAt with ⟨%wca, #Hwca, %Hwcaeq⟩
  wp_join iprop(∃ (gla gea : GoSlice) (pp : TermFn Int × TermFn Int),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      r_ptr.[G.MemResult, go!"LedAt"] ↦ gla ∗ r_ptr.[G.MemResult, go!"ElAt"] ↦ gea ∗
      termIntsRO gla pp.1 ∗ termIntsRO gea pp.2 ∗ ⌜jp2 pp = .ok r⌝)
    at next with [x s ev n RLedAt RElAt] as ⟨%gla, %gea, %pp, x, s, ev, n, RLedAt, RElAt, #Hla, #Hea, %Hjp2⟩
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_wins_unfold.method_unfold]
    try wp_auto
    wp_apply wp_wins _ _ w $$ [Hx]
    · iframe Hx; ipureintro; exact hw
    cases w
    · simp only [Bool.false_eq_true, ite_false] at Hjp
      wp_auto
      replace Hjp := bind_ok Hjp; obtain ⟨pp, hpp, Hjp⟩ := Hjp
      simp only [pure_ok, Except.ok.injEq] at hpp
      subst hpp
      wp_join_done
      iexists g.LedAt', g.ElAt', (s.ledAt, s.elAt)
      iframe
      isplitr; · iexact HLedAt
      isplitr; · iexact HElAt
      ipureintro; exact Hjp
    · simp only [ite_true] at Hjp
      wp_auto
      replace Hjp := bind_ok Hjp; obtain ⟨t, ht, Hjp⟩ := Hjp
      replace Hjp := bind_ok Hjp; obtain ⟨t', ht', Hjp⟩ := Hjp
      rw [ht] at ht'; cases ht'
      replace Hjp := bind_ok Hjp; obtain ⟨pp, hpp, Hjp⟩ := Hjp
      simp only [pure_ok, Except.ok.injEq] at hpp
      subst hpp
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
      try wp_auto
      wp_apply wp_T _ _ t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      wp_apply wp_load_at _ _ _ Hn $$ [Hwca] as -
      · iexact Hwca
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_With_unfold.method_unfold]
      try wp_auto
      wp_apply wp_With _ _ ut wca $$ [HLedAt] as %gla #Hgla
      · iframe HLedAt; ipureintro; have := HW.ledAt.1; omega
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
      try wp_auto
      wp_apply wp_T _ _ t $$ [Hx] as %ut2 %Hut2
      · iframe Hx; ipureintro; exact ht
      wp_apply wp_load_at _ _ _ Hn $$ [Hwca] as -
      · iexact Hwca
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_With_unfold.method_unfold]
      try wp_auto
      wp_apply wp_With _ _ ut2 wca $$ [HElAt] as %gea #Hgea
      · iframe HElAt; ipureintro; have := HW.elAt.1; omega
      wp_join_done
      iexists gla, gea, (s.ledAt.with (sint.Z ut) (sint.Z wca), s.elAt.with (sint.Z ut2) (sint.Z wca))
      iframe
      isplitr; · iexact Hgla
      isplitr; · iexact Hgea
      ipureintro; rw [Hut, Hut2, Hwcaeq]; exact Hjp
  clear Hjp
  obtain ⟨ledAt, elAt⟩ := pp
  simp -zeta only [jp2] at Hjp2
  replace Hjp2 := bind_ok Hjp2; obtain ⟨cd, hcd, Hjp2⟩ := Hjp2
  extract_lets jp3 at Hjp2
  ihave %Hchl := logRO_len _ _ $$ HChain
  wp_join iprop(∃ (gch : GoSlice) (ch : List Entry),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      r_ptr.[G.MemResult, go!"Chain"] ↦ gch ∗ logRO gch ch ∗ ⌜jp3 ch = .ok r⌝)
    at next with [x s ev n RChain] as ⟨%gch, %ch, x, s, ev, n, RChain, #Hch, %Hjp3⟩
  · obtain ⟨cm, hcm, hct, hcf⟩ := andM_ok hcd
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_cmt_unfold.method_unfold]
    try wp_auto
    wp_apply wp_cmt _ _ cm $$ [Hx]
    · iframe Hx; ipureintro; exact hcm
    cases cm
    · rw [hcf rfl] at Hjp2
      simp only [Bool.false_eq_true, ite_false] at Hjp2
      wp_auto
      replace Hjp2 := bind_ok Hjp2; obtain ⟨ch, hch, Hjp2⟩ := Hjp2
      simp only [pure_ok, Except.ok.injEq] at hch
      subst hch
      wp_join_done
      iexists g.Chain', s.chain
      iframe
      isplitr; · iexact HChain
      ipureintro; exact Hjp2
    · replace hct := bind_ok (hct rfl); obtain ⟨cv, hcv, hct⟩ := hct
      simp only [pure_ok, Except.ok.injEq] at hct
      wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]
      try wp_auto
      wp_apply wp_c _ _ cv $$ [Hx] as %uc %Huc
      · iframe Hx; ipureintro; exact hcv
      have hd : decide (sint.Z g.Chain'.len < sint.Z uc) = cd := by
        rw [Hchl, Huc, ← hct]
      rw [hd]
      cases cd
      · simp only [Bool.false_eq_true, ite_false] at Hjp2
        wp_auto
        replace Hjp2 := bind_ok Hjp2; obtain ⟨ch, hch, Hjp2⟩ := Hjp2
        simp only [pure_ok, Except.ok.injEq] at hch
        subst hch
        wp_join_done
        iexists g.Chain', s.chain
        iframe
        isplitr; · iexact HChain
        ipureintro; exact Hjp2
      · simp only [ite_true] at Hjp2
        wp_auto
        replace Hjp2 := bind_ok Hjp2; obtain ⟨ch, hch, Hjp2⟩ := Hjp2
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_newC_unfold.method_unfold]
        try wp_auto
        wp_apply wp_newC _ _ ch $$ [Hx] as %gch #Hgch
        · iframe Hx; ipureintro; exact hch
        wp_join_done
        iexists gch, ch
        iframe
        isplitr; · iexact Hgch
        ipureintro; exact Hjp2
  clear Hjp2
  simp -zeta only [jp3] at Hjp3
  replace Hjp3 := bind_ok Hjp3; obtain ⟨cm, hcm, Hjp3⟩ := Hjp3
  extract_lets jp4 at Hjp3
  wp_join iprop(∃ (gtl : GoSlice) (tl : TermFn Int),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      r_ptr.[G.MemResult, go!"TermLen"] ↦ gtl ∗ termIntsRO gtl tl ∗ ⌜jp4 tl = .ok r⌝)
    at next with [x s ev n RTermLen] as ⟨%gtl, %tl, x, s, ev, n, RTermLen, #Htl, %Hjp4⟩
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_cmt_unfold.method_unfold]
    try wp_auto
    wp_apply wp_cmt _ _ cm $$ [Hx]
    · iframe Hx; ipureintro; exact hcm
    cases cm
    · simp only [Bool.false_eq_true, ite_false] at Hjp3
      wp_auto
      replace Hjp3 := bind_ok Hjp3; obtain ⟨tl, htl, Hjp3⟩ := Hjp3
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      wp_join_done
      iexists g.TermLen', s.termLen
      iframe
      isplitr; · iexact HTermLen
      ipureintro; exact Hjp3
    · simp only [ite_true] at Hjp3
      wp_auto
      replace Hjp3 := bind_ok Hjp3; obtain ⟨t, ht, Hjp3⟩ := Hjp3
      replace Hjp3 := bind_ok Hjp3; obtain ⟨cv, hcv, Hjp3⟩ := Hjp3
      replace Hjp3 := bind_ok Hjp3; obtain ⟨tl, htl, Hjp3⟩ := Hjp3
      simp only [pure_ok, Except.ok.injEq] at htl
      subst htl
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
      try wp_auto
      wp_apply wp_T _ _ t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]
      try wp_auto
      wp_apply wp_c _ _ cv $$ [Hx] as %uc %Huc
      · iframe Hx; ipureintro; exact hcv
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_With_unfold.method_unfold]
      try wp_auto
      wp_apply wp_With _ _ ut uc $$ [HTermLen] as %gtl #Hgtl
      · iframe HTermLen; ipureintro; have := HW.termLen.1; omega
      wp_join_done
      iexists gtl, s.termLen.with (sint.Z ut) (sint.Z uc)
      iframe
      isplitr; · iexact Hgtl
      ipureintro; rw [Hut, Huc]; exact Hjp3
  clear Hjp3
  simp -zeta only [jp4] at Hjp4
  replace Hjp4 := bind_ok Hjp4; obtain ⟨d1, hd1, Hjp4⟩ := Hjp4
  extract_lets jpF jpU jp5 at Hjp4
  have hvl := HW.viol
  wp_join iprop(∃ (gv : GoSlice) (v : SSet),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      viol_ptr ↦ gv ∗ strsRO gv v ∗ ⌜v.length ≤ s.viol.length + 1 ∧ jp5 () v = .ok r⌝)
    at next with [x s ev n viol] as ⟨%gv, %v1, x, s, ev, n, viol, #Hv1, %Hjp5⟩
  · obtain ⟨cm, hcm, hct, hcf⟩ := andM_ok hd1
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_cmt_unfold.method_unfold]
    try wp_auto
    wp_apply wp_cmt _ _ cm $$ [Hx]
    · iframe Hx; ipureintro; exact hcm
    cases cm
    · rw [hcf rfl] at Hjp4
      simp only [Bool.false_eq_true, ite_false] at Hjp4
      wp_auto
      wp_join_done
      iexists g.Viol', viol0
      iframe
      isplitr; · iexact HViol
      ipureintro; exact ⟨by simp [viol0], Hjp4⟩
    · replace hct := bind_ok (hct rfl); obtain ⟨cmp, hcmp, hct⟩ := hct
      simp only [pure_ok, Except.ok.injEq] at hct
      wp_auto
      replace hcmp := bind_ok hcmp; obtain ⟨nc, hnc, hcmp⟩ := hcmp
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_newC_unfold.method_unfold]
      try wp_auto
      wp_apply wp_newC _ _ nc $$ [Hx] as %gnc #Hgnc
      · iframe Hx; ipureintro; exact hnc
      wp_apply wp_Comparable _ _ _ _ cmp $$ [HChain Hgnc]
      · iframe HChain Hgnc; ipureintro; exact hcmp
      subst hct
      cases cmp
      · simp only [Bool.not_false, ite_true] at Hjp4
        wp_auto
        wp_apply wp_violAdd _ _ _ $$ [HViol] as %gv #Hgv
        · iframe HViol; ipureintro; omega
        wp_join_done
        iexists gv, vCS
        iframe
        isplitr; · iexact Hgv
        ipureintro; exact ⟨setAdd_length_le _ _, Hjp4⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hjp4
        wp_auto
        wp_join_done
        iexists g.Viol', viol0
        iframe
        isplitr; · iexact HViol
        ipureintro; exact ⟨by simp [viol0], Hjp4⟩
  clear Hjp4
  simp -zeta only [jp5] at Hjp5
  obtain ⟨hv1, Hjp5⟩ := Hjp5
  replace Hjp5 := bind_ok Hjp5; obtain ⟨d2, hd2, Hjp5⟩ := Hjp5
  extract_lets vLC jp7 jp6 at Hjp5
  wp_join iprop(∃ (lcv : Bool),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      lc_ptr ↦ lcv ∗ ⌜jp6 () lcv = .ok r⌝)
    at next with [x s ev n lc] as ⟨%lcv, x, s, ev, n, lc, %Hjp6⟩
  · rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_cmt_unfold.method_unfold]
    try wp_auto
    wp_apply wp_cmt _ _ d2 $$ [Hx]
    · iframe Hx; ipureintro; exact hd2
    cases d2
    · simp only [Bool.false_eq_true, ite_false] at Hjp5
      wp_auto
      wp_join_done
      iexists false
      iframe
      ipureintro; exact Hjp5
    simp only [ite_true] at Hjp5
    replace Hjp5 := bind_ok Hjp5; obtain ⟨l, hl, Hjp5⟩ := Hjp5
    replace Hjp5 := bind_ok Hjp5; obtain ⟨lcv, hany, Hjp5⟩ := Hjp5
    wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_ll2_unfold.method_unfold]
    try wp_auto
    wp_apply wp_ll2 _ _ l $$ [Hx] as %gl #Hgl
    · iframe Hx; ipureintro; exact hl
    iunfold termLogsRO at Hgl
    icases Hgl with ⟨%gs, #Hgs, #Hgb⟩
    ihave %Hgsl := ownSlice_len _ _ _ $$ Hgs
    ihave %Hgbl := BigSepL2.bigSepL2_length $$ Hgb
    ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "p" ∷ (∃ pv : G.TermLog, p_ptr ↦ pv) ∗
        "lc" ∷ lc_ptr ↦ false ∗
        "%Hj" ∷ ⌜j ≤ l.length ∧ anyM (l.drop j) (fun q => andM
          (do let t ← InMem.T { s := s, n := sint.nat n, ev := ev }; pure (decide (q.1 > t)))
          (notM (do let nc ← InMem.newC { s := s, n := sint.nat n, ev := ev }; isPrefix nc q.2))) = .ok lcv⌝ : IProp GF)
      $$ [i p lc]
    · iexists 0
      iframe
      isplitl [p]
      · iexists _; iexact p
      ipureintro; exact ⟨Nat.zero_le _, hany⟩
    wp_for HI
    obtain ⟨Hjle, Hjany⟩ := Hj
    by_cases hjl : j < l.length
    · have hc : sint.Z (W64 (j : Int)) < sint.Z gl.len := by word
      rw [decide_eq_true hc]
      simp only [↓reduceIte]
      wp_auto
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      icases p with ⟨%pv, p⟩
      icases bigSepL2_at (fun (g : G.TermLog) (q : Int × List Entry) => iprop(⌜sint.Z g.T' = q.1⌝ ∗ logRO g.L' q.2))
        gs l j hjl $$ Hgb with ⟨%gq, %Hgq, %HgqT, #HgqL⟩
      wp_apply wp_load_index gl (W64 (j : Int)) gs gq h0 (by rw [show sint.nat (W64 (j : Int)) = j by word]; exact Hgq) $$ [Hgs]
      · iexact Hgs
      rw [anyM_drop_succ l _ hjl] at Hjany
      replace Hjany := bind_ok Hjany; obtain ⟨fv, hfv, Hjany⟩ := Hjany
      obtain ⟨a, ha, hat, haf⟩ := andM_ok hfv
      replace ha := bind_ok ha; obtain ⟨t, ht, ha⟩ := ha
      simp only [pure_ok, Except.ok.injEq] at ha
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
      try wp_auto
      wp_apply wp_T _ _ t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      have hw1 : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      have hda : decide (sint.Z ut < sint.Z gq.T') = a := by rw [Hut, HgqT, ← ha]
      rw [hda]
      cases a
      · rw [haf rfl] at Hjany
        simp only [Bool.false_eq_true, ite_false] at Hjany
        wp_auto
        wp_for_post
        iframe
        iexists j + 1
        rw [hw1]
        iframe
        isplitl [p]
        · iexists _; iexact p
        ipureintro; exact ⟨hjl, Hjany⟩
      replace hat := hat rfl
      unfold notM at hat
      replace hat := bind_ok hat; obtain ⟨ip, hip, hat⟩ := hat
      replace hip := bind_ok hip; obtain ⟨nc, hnc, hip⟩ := hip
      simp only [pure_ok, Except.ok.injEq] at hat
      subst hat
      wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_newC_unfold.method_unfold]
      try wp_auto
      wp_apply wp_newC _ _ nc $$ [Hx] as %gnc #Hgnc
      · iframe Hx; ipureintro; exact hnc
      wp_apply wp_IsPrefix _ _ _ _ ip $$ [Hgnc HgqL]
      · iframe Hgnc HgqL; ipureintro; exact hip
      cases ip
      · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hjany
        subst Hjany
        wp_auto
        wp_for_post
        wp_join_done
        iexists true
        iframe
        ipureintro; exact Hjp5
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hjany
        wp_auto
        wp_for_post
        iframe
        iexists j + 1
        rw [hw1]
        iframe
        isplitl [p]
        · iexists _; iexact p
        ipureintro; exact ⟨hjl, Hjany⟩
    · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z gl.len := by word
      rw [decide_eq_false hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hjeq : j = l.length := by omega
      subst hjeq
      simp only [List.drop_length] at Hjany
      cases Hjany
      wp_join_done
      iexists false
      iframe
      ipureintro; exact Hjp5
  clear Hjp5
  simp -zeta only [jp6] at Hjp6
  replace Hjp6 := bind_ok Hjp6; obtain ⟨d3, hd3, Hjp6⟩ := Hjp6
  icases logsRO_at g.Log' s.log n ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩ $$ HLog with ⟨%glog, #Hglog, #Hlogn⟩
  wp_join iprop(∃ (lcv' : Bool),
      x_ptr ↦ ({ s' := p, n' := n, ev' := e } : G.inMem) ∗ s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      lc_ptr ↦ lcv' ∗ ⌜jp7 () lcv' = .ok r⌝)
    at next with [x s ev n lc] as ⟨%lcv', x, s, ev, n, lc, %Hjp7⟩
  · obtain ⟨nl, hnl, hdt, hdf⟩ := andM_ok hd3
    simp only [pure_ok, Except.ok.injEq] at hnl
    subst hnl
    cases lcv
    case true =>
      rw [hdf rfl] at Hjp6
      simp only [Bool.false_eq_true, ite_false] at Hjp6
      wp_auto
      wp_join_done
      iexists true
      iframe
      ipureintro; exact Hjp6
    simp only [Bool.not_false] at hdt
    replace hdt := hdt trivial
    wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_wins_unfold.method_unfold]
    try wp_auto
    wp_apply wp_wins _ _ d3 $$ [Hx]
    · iframe Hx; ipureintro; exact hdt
    cases d3
    · simp only [Bool.false_eq_true, ite_false] at Hjp6
      wp_auto
      wp_join_done
      iexists false
      iframe
      ipureintro; exact Hjp6
    simp only [ite_true] at Hjp6
    replace Hjp6 := bind_ok Hjp6; obtain ⟨lcv2, hany, Hjp6⟩ := Hjp6
    ihave #HTL := HTermLen
    iunfold termIntsRO at HTL
    icases HTL with ⟨%gs, #Hgs, %Hgr⟩
    ihave %Hgsl := ownSlice_len _ _ _ $$ Hgs
    have Hgbl := Hgr.length_eq
    wp_auto
    ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "p" ∷ (∃ pv : G.TermInt, p_ptr ↦ pv) ∗
        "lc" ∷ lc_ptr ↦ false ∗
        "%Hj" ∷ ⌜j ≤ s.termLen.length ∧ anyM (s.termLen.drop j) (fun q => andM
          (do let t ← InMem.T { s := s, n := sint.nat n, ev := ev }; pure (decide (q.1 < t)))
          (notM (do let sc ← subSeq s.chain 1 q.2; isPrefix sc s.log[sint.nat n]!))) = .ok lcv2⌝ : IProp GF)
      $$ [i p lc]
    · iexists 0
      iframe
      isplitl [p]
      · iexists _; iexact p
      ipureintro; exact ⟨Nat.zero_le _, hany⟩
    wp_for HI
    obtain ⟨Hjle, Hjany⟩ := Hj
    by_cases hjl : j < s.termLen.length
    · have hc : sint.Z (W64 (j : Int)) < sint.Z g.TermLen'.len := by word
      rw [decide_eq_true hc]
      simp only [↓reduceIte]
      wp_auto
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      icases p with ⟨%pv, p⟩
      have hjg : j < gs.length := by omega
      have HgqR := forall₂_getElem Hgr j hjg hjl
      wp_apply wp_load_index g.TermLen' (W64 (j : Int)) gs gs[j] h0
        (by rw [show sint.nat (W64 (j : Int)) = j by word]; exact List.getElem?_eq_getElem hjg) $$ [Hgs]
      · iexact Hgs
      have hq : s.termLen[j]! = s.termLen[j] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
      rw [anyM_drop_succ s.termLen _ hjl, hq] at Hjany
      replace Hjany := bind_ok Hjany; obtain ⟨fv, hfv, Hjany⟩ := Hjany
      obtain ⟨a, ha, hat, haf⟩ := andM_ok hfv
      replace ha := bind_ok ha; obtain ⟨t, ht, ha⟩ := ha
      simp only [pure_ok, Except.ok.injEq] at ha
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_T_unfold.method_unfold]
      try wp_auto
      wp_apply wp_T _ _ t $$ [Hx] as %ut %Hut
      · iframe Hx; ipureintro; exact ht
      have hw1 : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      have hda : decide (sint.Z gs[j].T' < sint.Z ut) = a := by rw [Hut, HgqR.1, ← ha]
      rw [hda]
      cases a
      · rw [haf rfl] at Hjany
        simp only [Bool.false_eq_true, ite_false] at Hjany
        wp_auto
        wp_for_post
        iframe
        iexists j + 1
        rw [hw1]
        iframe
        isplitl [p]
        · iexists _; iexact p
        ipureintro; exact ⟨hjl, Hjany⟩
      replace hat := hat rfl
      unfold notM at hat
      replace hat := bind_ok hat; obtain ⟨ip, hip, hat⟩ := hat
      replace hip := bind_ok hip; obtain ⟨sc, hsc, hip⟩ := hip
      simp only [pure_ok, Except.ok.injEq] at hat
      subst hat
      wp_auto
      wp_apply wp_SubSeq _ _ (W64 1) gs[j].V' sc $$ [HChain] as %gsc #Hgsc
      · iframe HChain; ipureintro; rw [sint_one, HgqR.2]; exact hsc
      wp_apply wp_load_at _ _ _ Hn $$ [Hglog] as -
      · iexact Hglog
      wp_apply wp_IsPrefix _ _ _ _ ip $$ [Hgsc Hlogn]
      · iframe Hgsc Hlogn; ipureintro; exact hip
      cases ip
      · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Hjany
        subst Hjany
        wp_auto
        wp_for_post
        wp_join_done
        iexists true
        iframe
        ipureintro; exact Hjp6
      · simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Hjany
        wp_auto
        wp_for_post
        iframe
        iexists j + 1
        rw [hw1]
        iframe
        isplitl [p]
        · iexists _; iexact p
        ipureintro; exact ⟨hjl, Hjany⟩
    · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z g.TermLen'.len := by word
      rw [decide_eq_false hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hjeq : j = s.termLen.length := by omega
      rw [hjeq] at Hjany
      simp only [List.drop_length] at Hjany
      cases Hjany
      wp_join_done
      iexists false
      iframe
      ipureintro; exact Hjp6
  clear Hjp6
  simp -zeta only [jp7] at Hjp7
  wp_join iprop(∃ (gv : GoSlice) (v : SSet),
      s_ptr ↦ p ∗ ev_ptr ↦ e ∗ n_ptr ↦ n ∗
      viol_ptr ↦ gv ∗ strsRO gv v ∗ ⌜v.length ≤ s.viol.length + 2 ∧ jpU () v = .ok r⌝)
    at next with [s ev n viol] as ⟨%gv2, %v2, s, ev, n, viol, #Hv2, %HjpU⟩
  · cases lcv'
    · simp only [Bool.false_eq_true, ite_false] at Hjp7
      wp_auto
      wp_join_done
      iexists gv, v1
      iframe
      isplitr; · iexact Hv1
      ipureintro; exact ⟨by omega, Hjp7⟩
    · simp only [ite_true] at Hjp7
      wp_auto
      wp_apply wp_violAdd _ _ _ $$ [Hv1] as %gv' #Hgv'
      · iframe Hv1; ipureintro; omega
      wp_join_done
      iexists gv', vLC
      iframe
      isplitr; · iexact Hgv'
      ipureintro
      exact ⟨by have := setAdd_length_le v1 [76#8, 101#8, 97#8, 100#8, 101#8, 114#8, 67#8, 111#8, 109#8,
        112#8, 108#8, 101#8, 116#8, 101#8, 110#8, 101#8, 115#8, 115#8]; simp only [vLC]; omega, Hjp7⟩
  clear Hjp7
  simp -zeta only [jpU] at HjpU
  replace HjpU := bind_ok HjpU; obtain ⟨rl, hrl, HjpU⟩ := HjpU
  trace_state
  sorry

end proof

end AntCheck
end EtcdGrove
end Perennial
