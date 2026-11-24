/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.ackAt()` (B 291-359, `OnDisk.ackAt`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__ackAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__below
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__last
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

theorem onDisk.ackAt.wp_proof
    (wp_below : onDisk.below.spec (GF := GF) (hG := hG))
    (wp_last : onDisk.last.spec (GF := GF) (hG := hG)) :
    onDisk.ackAt.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.ackAt at Hv
  obtain ⟨bl, hbl, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
  try wp_auto
  wp_apply wp_below gx x bl $$ [Hx]
  · iframe Hx; ipureintro; exact hbl
  try wp_auto
  cases bl
  · simp only [Bool.false_eq_true, ite_false] at Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_last_unfold.method_unfold]
    try wp_auto
    wp_apply wp_last gx x v $$ [Hx] as %u %Hu
    · iframe Hx; ipureintro; exact Hv
    try wp_auto
    iapply HΦ; ipureintro; exact Hu
  · simp only [ite_true, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    ihave #Hs' := Hs
    iunfold stateRO at Hs'
    iNamed Hs'
    iNamed Hf
    iStructNamed Hp
    icases intsRO_at g.CommitIndex' x.s.commitIndex gx.n' ⟨Hn0, by rw [HWf.len_commitIndex]; omega⟩ $$ HCommitIndex with ⟨%ci, #Hci, %Hci⟩
    try wp_auto
    wp_apply wp_load_at _ _ ci Hn0 $$ [Hci]
    · iexact Hci
    try wp_auto
    rw [hnn] at Hci
    iapply HΦ; ipureintro; exact Hci

end proof

end AntCheck
end EtcdGrove
end Perennial
