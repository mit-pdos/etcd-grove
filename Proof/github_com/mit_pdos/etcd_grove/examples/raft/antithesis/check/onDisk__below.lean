/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.below()` (B 291-359, `OnDisk.below`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__isApp
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
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

theorem onDisk.below.wp_proof (wp_isApp : onDisk.isApp.spec (GF := GF) (hG := hG))
    (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG)) :
    onDisk.below.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.below at Hv
  obtain ⟨a, ha, ht, hf⟩ := andM_ok Hv
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'isApp.method_unfold]
  try wp_auto
  wp_apply wp_isApp gx x a $$ [Hx]
  · iframe Hx; ipureintro; exact ha
  cases a
  · rw [hf rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  have Hr := ht rfl
  obtain ⟨fm, hfm, Hr⟩ := bind_ok Hr
  simp only [pure_ok, Except.ok.injEq] at Hr
  subst Hr
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'fm.method_unfold]
  try wp_auto
  wp_apply wp_fm gx x fm $$ [Hx] as %u #Hu
  · iframe Hx; ipureintro; exact hfm
  iunfold appendFactRO at Hu
  icases Hu with ⟨%Hur, #-⟩
  icases intsRO_at g.CommitIndex' x.s.commitIndex gx.n' ⟨Hn0, by rw [HWf.len_commitIndex]; omega⟩ $$ HCommitIndex with ⟨%ci, #Hci, %Hci⟩
  try wp_auto
  wp_apply wp_load_at _ _ ci Hn0 $$ [Hci]
  · iexact Hci
  try wp_auto
  rw [hnn] at Hci
  rw [Hur.2.2.2.1, Hci]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
