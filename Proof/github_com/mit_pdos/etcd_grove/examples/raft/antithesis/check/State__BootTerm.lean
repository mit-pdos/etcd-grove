/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `State.BootTerm` (B 96).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__BootTerm
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

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

theorem State.BootTerm.wp_proof : State.BootTerm.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #-, #-, %Hb⟩
  iStructNamed Hgc
  wp_auto
  cases hB : gc.Bootstrapped' <;> rw [hB] at Hb <;> wp_auto <;> iapply HΦ <;> ipureintro <;>
    simp [State.bootTerm, ← Hb]

end proof

end AntCheck
end EtcdGrove
end Perennial
