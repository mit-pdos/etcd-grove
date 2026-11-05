/- Lean-first (no Rocq counterpart). The proof of `writer.checkHook`: the counter's load (owned),
then the check. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem writer.checkHook.wp_proof (wp_check : check.spec (GF := GF) (hG := hG)) :
    writer.checkHook.spec (GF := GF) (hG := hG) := by
  intro w wv dq i
  wp_start as ⟨Hw, Hs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamedSuffix Hw "W"
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Load wv.saved' (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists i
  iframe
  iintro Hs
  imod Hcl with -
  imodintro
  wp_auto
  wp_apply wp_check
  · itrivial
  (try wp_auto)
  ihave Hw : w ↦{dq} wv $$ [kvW leW hW rW leasesW nextIDW valsW applyingW savedW ticksW]
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef, named]
    iframe
  iapply HΦ
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
