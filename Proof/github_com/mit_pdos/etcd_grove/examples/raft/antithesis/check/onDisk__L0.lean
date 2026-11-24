/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.L0()` (B 291-359, `OnDisk.L0`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L0
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

theorem onDisk.L0.wp_proof : onDisk.L0.spec (GF := GF) (hG := hG) := by
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
  icases logsRO_at g.Log' x.s.log gx.n' ⟨Hn0, by rw [HWf.len_log]; omega⟩ $$ HLog with ⟨%lv, #Hla, #Hl⟩
  wp_auto
  wp_apply wp_load_at _ _ lv Hn0 $$ [Hla]
  · iexact Hla
  try wp_auto
  iapply HΦ
  rw [show x.L0 = x.s.log[sint.nat gx.n']! by rw [hnn]; rfl]
  iexact Hl

end proof

end AntCheck
end EtcdGrove
end Perennial
