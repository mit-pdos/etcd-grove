/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/ValidateConfig.lean (241f27e).
-/
/-
The proof of `raft.ValidateConfig`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.ValidateConfig
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.ValidateConfig.wp_proof :
    github_com.hashicorp.raft.ValidateConfig.spec (GF := GF) (hG := hG) := by
  intro cp c dq i
  wp_start as ⟨Hc, %Hok⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hc with ⟨Hc, %Hcn⟩
  iStructNamed Hc
  wp_auto
  simp only [ProtocolVersionMin, ProtocolVersionMax, time.Millisecond]
  wp_auto
  obtain ⟨hpv, hid, hine, -, -, -, -, -, hm1, hm2, hh, hhe, hct, hsi, hll, hllh, -, -, -, -⟩ := Hok
  subst hid
  rw [hpv]
  have hlen : (c.LocalID' : List w8).length ≠ 0 := by simpa using hine
  repeat' (first | (exfalso; word) | wp_if_destruct | wp_auto |
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsl)
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hcn
  simp only [TypedPointsto.typedPointstoDef]
  rw [hpv]
  iframe

end proof

end Perennial
