/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.T0()` (B 291-359, `OnDisk.T0`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T0
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

theorem onDisk.T0.wp_proof : onDisk.T0.spec (GF := GF) (hG := hG) := by
  intro gx x
  wp_start as #Hx
  iunfold onDiskRO at Hx
  icases Hx with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, -, -, -⟩ := Hp
  iunfold stateRO at Hs
  iNamed Hs
  iNamed Hf
  iStructNamed Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  icases intsRO_at g.CurrentTerm' x.s.currentTerm gx.n' ⟨Hn0, by rw [HWf.len_currentTerm]; omega⟩ $$ HCurrentTerm with ⟨%ct, #Hct, %Hct⟩
  wp_auto
  wp_apply wp_load_at _ _ ct Hn0 $$ [Hct]
  · iexact Hct
  try wp_auto
  iapply HΦ; ipureintro
  rw [Hct, hnn]; rfl

end proof

end AntCheck
end EtcdGrove
end Perennial
