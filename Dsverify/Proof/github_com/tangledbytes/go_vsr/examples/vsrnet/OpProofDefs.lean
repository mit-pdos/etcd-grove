/-
The definitions, specs and lemmas of `OpProof.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientDefs
public import Perennial.Spec.time.Sleep
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- The slot's update as the ghost layer's (`lin_AUof`; a read's persistent one, used once). -/
theorem slotUpd_AUof (g : Impl.GN) (i : KIn) (Φ : KOut → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (kvR g) i Φ ⊢ Impl.AUof g i.1 (fun _ _ o => Φ (bndO o)) := by
  cases hw : (kvR (GF := GF) (Gg := hG.goose_globalGS) g).B.isWrite i
  · rw [slotUpd_read _ hw]
    iintro #H
    iapply lin_AUof
    iexact H
  · rw [slotUpd_write _ hw]
    iintro H
    iapply lin_AUof
    iexact H

/-- **`Op(sys, in)`, one call** (see the file header). -/
abbrev Op.spec : Prop :=
  ∀ (γ : Names) (c n : Nat) (sys : GoInterface) (i : KIn) (Φ : KOut → IProp GF),
  c < 6 → n < 2 ^ 28 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ sysRes γ c sys n ∗
      slotUpd (Gg := hG.goose_globalGS) (kvR γ.gn) i Φ }}
    (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Op)) (Val #sys))
      (Val #((kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).iv i)))
  {{ (v : GoInterface), RET #v; ∃ n', ⌜n ≤ n' ∧ n' ≤ n + 1⌝ ∗ sysRes γ c sys n' ∗
      ((∃ o, ⌜v = (kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).ov o⌝ ∗ Φ o) ∨
        ⌜v = (kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).unk i⌝) }}

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
