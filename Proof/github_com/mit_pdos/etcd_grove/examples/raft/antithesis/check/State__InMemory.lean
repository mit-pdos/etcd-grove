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
  trace_state
  sorry

end proof

end AntCheck
end EtcdGrove
end Perennial
