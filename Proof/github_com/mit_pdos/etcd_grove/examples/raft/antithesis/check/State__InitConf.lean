/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): the proof of `State.InitConf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__InitConf
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

theorem State.InitConf.wp_proof : State.InitConf.spec (GF := GF) (hG := hG) := by
  intro p s
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hc, #Hsv, #Hiv, %Hb⟩
  iStructNamed Hc
  wp_auto
  iapply HΦ
  iunfold confRO
  simp only [State.initConf, Config.initConf]
  isplitr
  · iexact Hiv
  iunfold strsRO
  iapply ownSlice_nil

end proof

end AntCheck
end EtcdGrove
end Perennial
