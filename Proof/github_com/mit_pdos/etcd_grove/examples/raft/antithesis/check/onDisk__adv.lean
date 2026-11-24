/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.adv()` (B 291-359, `OnDisk.adv`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__adv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
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

theorem onDisk.adv.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG)) :
    onDisk.adv.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.adv at Hv
  obtain ⟨y, hy, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  icases intsRO_at g.CommitIndex' x.s.commitIndex gx.n' ⟨Hn0, by rw [HWf.len_commitIndex]; omega⟩ $$ HCommitIndex with ⟨%ci, #Hci, %Hci⟩
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
  try wp_auto
  wp_apply wp_w gx x $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  wp_apply wp_commit e x.w y $$ [He] as %u %Hu
  · iframe He; ipureintro; exact hy
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn0 $$ [Hci]
  · iexact Hci
  try wp_auto
  rw [hnn] at Hci
  rw [Hu, Hci]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
