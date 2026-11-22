/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/promreg/NewRegistry.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.promreg.NewRegistry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [promG : promreg.PromRegGS GF]
variable [package_sem : promreg.Assumptions]

theorem promreg.NewRegistry.wp_proof : promreg.NewRegistry.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %mI HmI
  wp_apply wp_map_make1 (K := GoString) (V := w64) as %mD HmD
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %mC HmC
  iStructNamed «$r0»
  ipersist descIDs
  ipersist dimHashesByName
  ipersist collectorsByID
  imod (sync.init_Mutex (promreg.regInv (GF := GF) f mI mD mC) ⊤ _) $$ mu [HmI HmD HmC] with #Hmu
  · inext
    unfold promreg.regInv
    iexists ∅, ∅, ∅
    iframe
    isplitl []
    · rw [show ((∅ : GMap w64 Bool) ∪ ∅) = ∅ from by ext k; simp]
      iapply BigSepM.bigSepM_empty.2; iempintro
    ipureintro
    refine ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩
  imodintro
  iapply HΦ
  unfold promreg.isRegistry
  iexists mI, mD, mC
  iframe #

end proof

end EtcdGrove
end Perennial
