/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.old()` (B 291-359, `OnDisk.old`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__old
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Get
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

theorem onDisk.old.wp_proof
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG))
    (wp_Has : TermInts.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermInts.Get.spec (GF := GF) (hG := hG)) :
    onDisk.old.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.old at Hv
  obtain ⟨t1, ht1, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
  try wp_auto
  wp_apply wp_T1 gx x t1 $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_unfold'Has.method_unfold]
  try wp_auto
  wp_apply wp_Has gx.tl' x.tl ut $$ [Htl]
  · iexact Htl
  rw [Hut]
  cases hh : x.tl.has t1
  · simp only [hh, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; rfl
  · simp only [hh, ite_true] at Hv
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
    try wp_auto
    wp_apply wp_T1 gx x t1 $$ [Hx] as %ut2 %Hut2
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_unfold'Get.method_unfold]
    try wp_auto
    wp_apply wp_Get gx.tl' x.tl ut2 v $$ [Htl] as %u %Hu
    · iframe Htl; ipureintro; rw [Hut2]; exact Hv
    try wp_auto
    iapply HΦ; ipureintro; exact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
