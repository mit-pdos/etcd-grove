/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.ch1()` (B 291-359, `OnDisk.ch1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__ch1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__adv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__newC
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

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

theorem onDisk.ch1.wp_proof
    (wp_adv : onDisk.adv.spec (GF := GF) (hG := hG))
    (wp_newC : onDisk.newC.spec (GF := GF) (hG := hG)) :
    onDisk.ch1.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, -, -, HB⟩ := Hp
  obtain ⟨b, E, hb, HW⟩ := HB.get
  have hb' := hb; unfold numBound at hb'
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  unfold OnDisk.ch1 at Hv
  obtain ⟨c, hc, Hv⟩ := bind_ok Hv
  obtain ⟨ad, had, ht, hf⟩ := andM_ok hc
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_adv_unfold.method_unfold]
  try wp_auto
  wp_apply wp_adv gx x ad $$ [Hx]
  · iframe Hx; ipureintro; exact had
  try wp_auto
  cases ad
  · rw [hf rfl] at Hv
    simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; iexact Hch
  · have hc2 := ht rfl
    obtain ⟨nc, hnc, hc2⟩ := bind_ok hc2
    simp only [pure_ok, Except.ok.injEq] at hc2
    subst hc2
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_newC_unfold.method_unfold]
    try wp_auto
    wp_apply wp_newC gx x nc $$ [Hx] as %ncl #Hnc
    · iframe Hx; ipureintro; exact hnc
    try wp_auto
    ihave %Hncl := logRO_len _ _ $$ Hnc
    ihave %Hchl := logRO_len _ _ $$ Hch
    rw [Hncl, Hchl]
    by_cases hgt : (x.ch.length : Int) < nc.length
    · rw [decide_eq_true hgt]
      have hgt' : decide (nc.length > x.ch.length) = true := by simp; omega
      rw [hgt'] at Hv
      simp only [ite_true] at Hv
      try wp_auto
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_newC_unfold.method_unfold]
      try wp_auto
      wp_apply wp_newC gx x v $$ [Hx] as %ncl2 #Hnc2
      · iframe Hx; ipureintro; exact Hv
      try wp_auto
      iapply HΦ; iexact Hnc2
    · rw [decide_eq_false hgt]
      have hgt' : decide (nc.length > x.ch.length) = false := by simp; omega
      rw [hgt'] at Hv
      simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
      subst Hv
      try wp_auto
      iapply HΦ; iexact Hch

end proof

end AntCheck
end EtcdGrove
end Perennial
