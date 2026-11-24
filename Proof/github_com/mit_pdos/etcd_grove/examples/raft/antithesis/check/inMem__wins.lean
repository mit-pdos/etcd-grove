/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.wins()` (B 214-230, `InMem.wins`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__wins
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__leads
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

theorem inMem.wins.wp_proof
    (wp_leads : inMem.leads.spec (GF := GF) (hG := hG)) :
    inMem.wins.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.wins at Hv
  obtain ⟨l, hl, ht, hf⟩ := andM_ok Hv
  obtain ⟨Hn, Hlt, -⟩ := Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  iunfold stateRO at Hs
  iNamed Hs
  iNamed Hf
  iStructNamed Hp
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
    simp only [pure_ok, Except.ok.injEq] at Hr
    subst Hr
    ihave #Hrla := strsRO_at g.Role' x.s.role gx.n' ⟨Hn0, by rw [HWf.len_role]; omega⟩ $$ HRole
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn0 $$ [Hrla] as -
    · iexact Hrla
    try wp_auto
    rw [hnn, not_decide_eq_bne]
    unfold leader
    iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
