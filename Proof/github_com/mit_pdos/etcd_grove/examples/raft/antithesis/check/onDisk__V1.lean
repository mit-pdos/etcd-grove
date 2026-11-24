/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.V1()` (B 291-359, `OnDisk.V1`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__V1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__Vote
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.V1.wp_proof (wp_T0 : onDisk.T0.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG)) (wp_Vote : State.Vote.spec (GF := GF) (hG := hG)) :
    onDisk.V1.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, Hmore, Hrol, HB⟩ := Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  unfold OnDisk.V1 at Hv
  obtain ⟨t1, ht1, Hv⟩ := bind_ok Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
  try wp_auto
  wp_apply wp_T1 gx x t1 $$ [Hx] as %u1 %Hu1
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T0.method_unfold]
  try wp_auto
  wp_apply wp_T0 gx x $$ [Hx] as %u0 %Hu0
  · iexact Hx
  try wp_auto
  rw [decide_w64_eq, Hu1, Hu0]
  by_cases he : t1 = x.T0
  · rw [decide_eq_true he]
    simp only [he, bne_self_eq_false, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    wp_apply wp_Vote gx.s' x.s gx.n' $$ [Hs]
    · iframe Hs; ipureintro; exact ⟨Hn0, by omega⟩
    try wp_auto
    rw [hnn]
    iapply HΦ; ipureintro; trivial
  rw [decide_eq_false he]
  simp only [bne_iff_ne, ne_eq, he, not_false_eq_true, ite_true, pure_ok, Except.ok.injEq] at Hv
  subst Hv
  try wp_auto
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
