/-
Lean-first (no Rocq counterpart).

# Halves of a map points-to (2026-10-29, track C)

The applier and a replica's lock each hold half of the applied table (`repOwn`, `repShared`); a
write combines them (`ownMap_halves_combine`) and splits them back (`ownMap_halves_split`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode

section halves
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem ownMap_halves_split (mref : Loc) (A : GMap (List w8) (List w8)) :
    mref ↦$ A ⊢ (mref ↦${DFrac.own (1 : Qp).half} A ∗ mref ↦${DFrac.own (1 : Qp).half} A :
      IProp GF) := by
  have h := (ownMap_fractional (GF := GF) mref A).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem ownMap_halves_combine (mref : Loc) (A A' : GMap (List w8) (List w8)) :
    (mref ↦${DFrac.own (1 : Qp).half} A ∗ mref ↦${DFrac.own (1 : Qp).half} A' : IProp GF) ⊢
      ⌜A = A'⌝ ∗ mref ↦$ A := by
  have h := (ownMap_fractional (GF := GF) mref A).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iintro ⟨H1, H2⟩
  ihave %Heq := ownMap_agree mref _ _ A A' $$ [H1 H2]
  · iframe
  subst Heq
  isplitr
  · ipureintro; rfl
  iapply h.2
  iframe

end halves

end kvreconf
end EtcdGrove
end Perennial
