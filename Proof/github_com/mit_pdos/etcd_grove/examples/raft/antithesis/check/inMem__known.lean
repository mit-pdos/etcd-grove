/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.known()` (B 214-230, `InMem.known`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__known
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__T
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__Get
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

theorem inMem.known.wp_proof
    (wp_T : inMem.T.spec (GF := GF) (hG := hG))
    (wp_Has : TermInts.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermInts.Get.spec (GF := GF) (hG := hG)) :
    inMem.known.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.known at Hv
  obtain ⟨t, ht, Hv⟩ := bind_ok Hv
  iunfold stateRO at Hs
  iNamed Hs
  iNamed Hf
  iStructNamed Hp
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'T.method_unfold]
  try wp_auto
  wp_apply wp_T gx x t $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_unfold'Has.method_unfold]
  try wp_auto
  wp_apply wp_Has g.TermLen' x.s.termLen ut $$ [HTermLen]
  · iexact HTermLen
  rw [Hut]
  cases hh : x.s.termLen.has t
  · simp only [hh, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; ipureintro; rfl
  · simp only [hh, ite_true] at Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_unfold'T.method_unfold]
    try wp_auto
    wp_apply wp_T gx x t $$ [Hx] as %ut2 %Hut2
    · iframe Hx; ipureintro; exact ht
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts.TypeAssumptions.ptr_unfold'Get.method_unfold]
    try wp_auto
    wp_apply wp_Get g.TermLen' x.s.termLen ut2 v $$ [HTermLen] as %u %Hu
    · iframe HTermLen; ipureintro; rw [Hut2]; exact Hv
    try wp_auto
    iapply HΦ; ipureintro; exact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
