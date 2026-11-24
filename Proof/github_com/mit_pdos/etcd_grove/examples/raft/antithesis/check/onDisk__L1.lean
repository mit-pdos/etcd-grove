/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.L1()` (B 291-359, `OnDisk.L1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat
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

theorem onDisk.L1.wp_proof
    (wp_stores : onDisk.stores.spec (GF := GF) (hG := hG))
    (wp_L0 : onDisk.L0.spec (GF := GF) (hG := hG))
    (wp_first : onDisk.first.spec (GF := GF) (hG := hG))
    (wp_es : onDisk.es.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_Concat : Concat.spec (GF := GF) (hG := hG)) :
    onDisk.L1.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.L1 at Hv
  obtain ⟨st, hst, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_stores_unfold.method_unfold]
  try wp_auto
  wp_apply wp_stores gx x st $$ [Hx]
  · iframe Hx; ipureintro; exact hst
  try wp_auto
  cases st
  · simp only [Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_L0_unfold.method_unfold]
    try wp_auto
    wp_apply wp_L0 gx x  $$ [Hx] as %l0 #Hl0
    · iexact Hx
    try wp_auto
    iapply HΦ; iexact Hl0
  · simp only [ite_true] at Hv
    obtain ⟨fi, hfi, Hv⟩ := bind_ok Hv
    obtain ⟨pre, hpre, Hv⟩ := bind_ok Hv
    obtain ⟨es, hes, Hv⟩ := bind_ok Hv
    simp only [pure_ok, Except.ok.injEq] at Hv
    subst Hv
    have hfb := OnDisk.first_bounds hb HW hfi
    have hesl := OnDisk.es_le HW hes
    have hl0 := OnDisk.L0_le HW
    have hprel := subSeq_length_le hpre
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_L0_unfold.method_unfold]
    try wp_auto
    wp_apply wp_L0 gx x  $$ [Hx] as %l0 #Hl0
    · iexact Hx
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_first_unfold.method_unfold]
    try wp_auto
    wp_apply wp_first gx x fi $$ [Hx] as %ufi %Hufi
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    have Hfi : sint.Z (ufi - W64 1) = fi - 1 := by
      rw [sint_sub (by rw [Hufi, sint_one]; omega) (by rw [Hufi, sint_one]; omega), Hufi, sint_one]
    wp_apply wp_SubSeq l0 x.L0 (W64 1) (ufi - W64 1) pre $$ [Hl0] as %pl #Hpl
    · iframe Hl0; ipureintro; rw [Hfi]; exact hpre
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_es_unfold.method_unfold]
    try wp_auto
    wp_apply wp_es gx x es $$ [Hx] as %esl #Hes
    · iframe Hx; ipureintro; exact hes
    try wp_auto
    wp_apply wp_Concat pl pre esl es $$ [Hpl Hes] as %r #Hr
    · iframe Hpl Hes; ipureintro; omega
    try wp_auto
    iapply HΦ; iexact Hr

end proof

end AntCheck
end EtcdGrove
end Perennial
