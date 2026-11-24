/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `Value.rec`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value__rec

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

theorem Value.rec.wp_proof : Value.rec.spec (GF := GF) (hG := hG) := by
  intro g v w
  wp_start as ⟨#Hv, %Hw⟩
  have hrec : v.isRec = true := by
    unfold Value.asRec at Hw
    cases h : v.isRec
    · rw [h] at Hw; cases Hw
    · rfl
  have hvw : w = v := by
    unfold Value.asRec at Hw
    rw [hrec] at Hw; cases Hw; rfl
  subst hvw
  ihave #Hv0 := Hv
  iunfold valueRO at Hv0
  icases Hv0 with ⟨%Hv1, -, -⟩
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ v with ⟨v, %Hnn⟩
  iStructNamed v
  try wp_auto
  rw [Hv1.1, hrec]
  try wp_auto
  ihave v : (v_ptr ↦ g : IProp GF) $$ [IsRec Str Add Remove Joint Leave]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    rw [Hv1.1, hrec]
    iframe
  try wp_auto
  iapply HΦ; iexact Hv

end proof

end AntCheck
end EtcdGrove
end Perennial
