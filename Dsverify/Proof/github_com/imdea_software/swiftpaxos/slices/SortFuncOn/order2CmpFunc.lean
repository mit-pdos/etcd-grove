/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/slices/SortFuncOn/order2CmpFunc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Perennial's `slices.order2CmpFunc` spec and proof (Perennial/Spec/slices/order2CmpFunc.lean,
Perennial/Proof/slices/order2CmpFunc.lean) with the comparator needed only on `φ`, which every element
of the slice satisfies (Proof/slices/SortFuncOn/Basics.lean).
-/
module

public import Perennial.Proof.slices.SortBasics
public import Perennial.Spec.slices.order2CmpFunc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.Basics
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.slices.SortFuncOn.order2CmpFuncDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.order2CmpFunc.wp_proofOn : slices.order2CmpFunc.specOn (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R _ φ data a b swaps_l cmp_code dq xs swaps xa xb Ha_bound Hb_bound Hφ
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hxs
  have := lookup_lt_Some Hxa
  have := lookup_lt_Some Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z b) xs dq xb Hb_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxb
  slice_index_if
  wp_apply wp_load_slice_index data (sint.Z a) xs dq xa Ha_bound $$ [Hxs] with Hxs
  · iframe Hxs; ipureintro; exact Hxa
  wp_apply slices.cmpOn_wp R φ cmp_code xb xa (slices.allOn_lookup φ Hφ Hxb)
    (slices.allOn_lookup φ Hφ Hxa) $$ Hcmp with %r %Hr
  wp_if_destruct
  · iapply HΦ
    iframe
    ipureintro
    right; exact ⟨rfl, rfl, Hr.1 (by word)⟩
  · iapply HΦ
    iframe
    ipureintro
    left; exact ⟨rfl, rfl, fun h => Hif (by have := Hr.2 h; word)⟩

end proof

end Perennial
