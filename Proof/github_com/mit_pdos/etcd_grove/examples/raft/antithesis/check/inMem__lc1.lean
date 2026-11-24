/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.lc1()` (B 214-230, `InMem.lc1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__lc1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__wins
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs__With
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem inMem.lc1.wp_proof
    (wp_wins : inMem.wins.spec (GF := GF) (hG := hG))
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_With : TermConfs.With.spec (GF := GF) (hG := hG)) :
    inMem.lc1.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.lc1 at Hv
  obtain ⟨w, hw, Hv⟩ := bind_ok Hv
  obtain ⟨Hn, Hlt, HBd⟩ := Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  iunfold stateRO at Hs
  iNamed Hs
  iNamed Hf
  iStructNamed Hp
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'wins.method_unfold]
  try wp_auto
  wp_apply wp_wins gx x w $$ [Hx]
  · iframe Hx; ipureintro; exact hw
  try wp_auto
  cases w
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; iexact HLedConf
  · simp only [ite_true] at Hv
    obtain ⟨t, ht, Hv⟩ := bind_ok Hv
    simp only [pure_ok, Except.ok.injEq] at Hv
    subst Hv
    icases confsRO_at g.Config' x.s.config gx.n' ⟨Hn0, by rw [HWf.len_config]; omega⟩ $$ HConfig with ⟨%lg, #Hlga, #Hlg⟩
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'T.method_unfold]
    try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn0 $$ [Hlga] as -
    · iexact Hlga
    try wp_auto
    obtain ⟨bb, EE, HW, -, -, hbb, -⟩ := HBd
    have hlen := HW.ledConf_len
    unfold numBound at hbb
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermConfs.TypeAssumptions.ptr_unfold'With.method_unfold]
    try wp_auto
    wp_apply wp_With _ _ ut _ x.s.config[x.n]! $$ [HLedConf] as %u #Hu
    · iframe HLedConf; rw [← hnn]; iframe Hlg; ipureintro; omega
    try wp_auto
    rw [Hut]
    iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
