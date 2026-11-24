/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `IsConf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsConf

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

theorem IsConf.wp_proof : IsConf.spec (GF := GF) (hG := hG) := by
  intro g e
  wp_start as #He
  iunfold entryRO at He
  icases He with ⟨%Hx, -⟩
  wp_auto
  have : decide (g.Type' = go!"conf") = isConf e := by
    unfold isConf; rw [Hx.2]; cases h : (e.type == go!"conf") <;> simp_all
  rw [show ([99#8, 111#8, 110#8, 102#8] : List w8) = go!"conf" from rfl, this]
  iapply HΦ
  ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
