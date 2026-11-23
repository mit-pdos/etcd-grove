/-
The proof of `Net/Spec/models_lab/pbcodec/AppendBytes.lean`: `AppendVarint(b, uint64(len(v)))`,
then Go's `append` of `v`.
-/
module

public import Net.Spec.models_lab.pbcodec.AppendBytes
public import Net.Spec.models_lab.pbcodec.AppendVarint

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.pbcodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.pbcodec.Assumptions]

set_option goose.wp.extras true

theorem AppendBytes.wp_proof (wp_AppendVarint : AppendVarint.spec (GF := GF) (hG := hG)) :
    AppendBytes.spec (GF := GF) (hG := hG) := by
  intro b bs v dq vs
  wp_start as ⟨Hb, Hcap, Hv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_AppendVarint $$ [$Hb $Hcap] as %b1 ⟨Hb1, Hcap1⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hb1 $Hcap1 $Hv] as %b' ⟨Hb', Hcap', Hv⟩
  (try wp_auto)
  iapply HΦ
  have hl : uint.nat v.len = vs.length := by rw [Hlen.1]; word
  rw [hl, List.append_assoc]
  iframe

end proof

end models_lab.pbcodec
end Perennial
