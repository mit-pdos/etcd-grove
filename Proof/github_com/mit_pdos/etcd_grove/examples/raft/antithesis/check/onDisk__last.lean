/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.last()` (B 291-359, `OnDisk.last`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__last
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__f
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

theorem onDisk.last.wp_proof
    (wp_f : onDisk.f.spec (GF := GF) (hG := hG)) :
    onDisk.last.spec (GF := GF) (hG := hG) := by
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
  unfold OnDisk.last at Hv
  obtain ⟨f, hf, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  have hfw := OnDisk.f_within hb HW hf
  unfold bigOk at hfw
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'f.method_unfold]
  try wp_auto
  wp_apply wp_f gx x f $$ [Hx] as %u2 #Hu2
  · iframe Hx; ipureintro; exact hf
  try wp_auto
  iunfold appendFactRO at Hu2
  icases Hu2 with ⟨%Hur, #Hes⟩
  ihave %Hesl := logRO_len _ _ $$ Hes
  try wp_auto
  iapply HΦ; ipureintro
  rw [sint_add (by rw [Hur.2.2.2.1, Hesl]; omega) (by rw [Hur.2.2.2.1, Hesl]; omega), Hur.2.2.2.1, Hesl]

end proof

end AntCheck
end EtcdGrove
end Perennial
