/-
The proof of `Net/Spec/models_lab/pbcodec/AppendTag.lean`: `AppendVarint(b, num<<3|typ&7)`, the
word being `num * 8 + typ` for the bounds the spec takes.
-/
module

public import Net.Spec.models_lab.pbcodec.AppendTag
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

theorem AppendTag.wp_proof (wp_AppendVarint : AppendVarint.spec (GF := GF) (hG := hG)) :
    AppendTag.spec (GF := GF) (hG := hG) := by
  intro b bs num typ h1 h2
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_AppendVarint $$ [$Hb $Hcap] as %b' ⟨Hb', Hcap'⟩
  (try wp_auto)
  iapply HΦ
  rw [EtcdGrove.Wire.tag, ← tagWord num typ h1 h2]
  iframe

end proof

end models_lab.pbcodec
end Perennial
