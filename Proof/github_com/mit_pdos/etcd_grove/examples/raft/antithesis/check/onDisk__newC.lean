/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.newC()` (B 291-359, `OnDisk.newC`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__newC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
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

theorem onDisk.newC.wp_proof
    (wp_L1 : onDisk.L1.spec (GF := GF) (hG := hG))
    (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG)) :
    onDisk.newC.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.newC at Hv
  obtain ⟨l1, hl1, Hv⟩ := bind_ok Hv
  obtain ⟨c, hc, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'L1.method_unfold]
  try wp_auto
  wp_apply wp_L1 gx x l1 $$ [Hx] as %ul #Hul
  · iframe Hx; ipureintro; exact hl1
  try wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
  try wp_auto
  wp_apply wp_w gx x  $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  wp_apply wp_commit e x.w c $$ [He] as %uc %Huc
  · iframe He; ipureintro; exact hc
  try wp_auto
  wp_apply wp_SubSeq ul l1 (W64 1) uc v $$ [Hul] as %r #Hr
  · iframe Hul; ipureintro; rw [Huc]; exact Hv
  try wp_auto
  iapply HΦ; iexact Hr

end proof

end AntCheck
end EtcdGrove
end Perennial
