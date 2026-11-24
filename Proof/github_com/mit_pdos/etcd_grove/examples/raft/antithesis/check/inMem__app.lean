/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.app()` (B 214-230, `InMem.app`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__app
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__es
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

theorem inMem.app.wp_proof
    (wp_leads : inMem.leads.spec (GF := GF) (hG := hG))
    (wp_es : inMem.es.spec (GF := GF) (hG := hG)) :
    inMem.app.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.app at Hv
  obtain ⟨l, hl, ht, hf⟩ := andM_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_leads_unfold.method_unfold]
  try wp_auto
  wp_apply wp_leads gx x l $$ [Hx]
  · iframe Hx; ipureintro; exact hl
  try wp_auto
  cases l
  · rw [hf rfl]
    try wp_auto
    iapply HΦ; ipureintro; trivial
  · have Hr := ht rfl
    obtain ⟨es, hes, Hr⟩ := bind_ok Hr
    simp only [pure_ok, Except.ok.injEq] at Hr
    subst Hr
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem.TypeAssumptions.ptr_es_unfold.method_unfold]
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
