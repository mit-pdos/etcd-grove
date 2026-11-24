/-
Lean-first (no Rocq counterpart). #33 S3b W3a (2026-11-23): the proof of `x.newC()` (B 214-253, `InMem.newC`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__newC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__L
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__c
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws

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

theorem inMem.newC.wp_proof
    (wp_L : inMem.L.spec (GF := GF) (hG := hG))
    (wp_c : inMem.c.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG)) :
    inMem.newC.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  wp_auto
  unfold InMem.newC at Hv
  obtain ⟨l, hl, Hv⟩ := bind_ok Hv
  obtain ⟨c, hc, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_L_unfold.method_unfold]
  try wp_auto
  wp_apply wp_L gx x l $$ [Hx] as %ul #Hul
  · iframe Hx; ipureintro; exact hl
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_c_unfold.method_unfold]
  try wp_auto
  wp_apply wp_c gx x c $$ [Hx] as %uc %Huc
  · iframe Hx; ipureintro; exact hc
  try wp_auto
  wp_apply wp_SubSeq ul l (W64 1) uc v $$ [Hul] as %u #Hu
  · iframe Hul; ipureintro; rw [sint_one, Huc]; exact Hv
  try wp_auto
  iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
