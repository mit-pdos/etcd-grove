/-
The definitions, specs and lemmas of `CodecProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelProofDefs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost.Impl

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem inFields_bnd (i : KIn) :
    (inFields i.1).2.1.length < 256 ∧ (inFields i.1).2.2.length < 2 ^ 16 := by
  obtain ⟨i, -, hb, hk⟩ := i
  cases i <;> simp only [InputBounded] at hb <;> simp only [inFields, List.length_nil] at hk ⊢ <;> omega

/-- An output the codec meets is a short `Out`. -/
theorem outOk_out (g : GN) (x : GoInterface) (h : RBase.outOk (kvR (GF := GF) (Gg := hG.goose_globalGS) g) x) :
    ∃ u d f w, w.length < 2 ^ 16 ∧ x = outVal u d f w := by
  rcases h with ⟨o, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨_, _, _, _, outFields_bnd o, rfl⟩
  · exact ⟨true, false, false, [], by simp, rfl⟩

/-- `Codec()`: the map's codec. -/
abbrev Codec.spec : Prop :=
  ∀ g : GN,
  {{ isPkgInit (PROP := IProp GF) kpkg }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Codec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      codecOk (kvR (GF := GF) (Gg := hG.goose_globalGS) g) cd }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
