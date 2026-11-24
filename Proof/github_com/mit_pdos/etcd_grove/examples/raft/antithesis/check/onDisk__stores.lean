/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.stores()` (B 291-359, `OnDisk.stores`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__es
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

theorem onDisk.stores.wp_proof
    (wp_es : onDisk.es.spec (GF := GF) (hG := hG)) :
    onDisk.stores.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.stores at Hv
  obtain ⟨es, hes, Hv⟩ := bind_ok Hv
  simp only [pure_ok, Except.ok.injEq] at Hv
  subst Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'es.method_unfold]
  try wp_auto
  wp_apply wp_es gx x es $$ [Hx] as %u #Hu
  · iframe Hx; ipureintro; exact hes
  try wp_auto
  ihave %Hul := logRO_len _ _ $$ Hu
  have : (!decide (u.len = W64 0)) = (es.length != 0) := by
    by_cases h0 : es.length = 0
    · have : u.len = W64 0 := by have := Hul; rw [h0] at this; word
      simp [this, h0]
    · have : u.len ≠ W64 0 := by intro h; rw [h] at Hul; simp at Hul; omega
      rw [decide_eq_false this]; simpa using h0
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
