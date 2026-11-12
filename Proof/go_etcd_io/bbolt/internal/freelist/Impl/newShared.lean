/-
`newShared()` (`internal/freelist/shared.go`, U2's internal): a fresh `shared`, its fields but
`readonlyTXIDs` the empty state's with a nil `Interface`, and a nil `readonlyTXIDs`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev newShared.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val #(functions go_etcd_io.bbolt.internal.freelist.newShared [])) (Val #()))
  {{ (s : Loc), RET #s; ownSh s interface.nil FLPg.empty ∗
      structFieldRef shared go!"readonlyTXIDs" s ↦ slice.nil }}

theorem newShared.wp_proof : newShared.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %pe Hpe
  wp_apply wp_map_make1 (K := w64) (V := w64) as %al Hal
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %ca Hca
  iStructNamed «$r0»
  iclear «$res0»
  iapply HΦ
  iframe
  iunfold ownSh
  iexists ∅
  isplitl [Hal Hca Hpe Interface allocs cache pending]
  · iunfold ownShC
    iexists al, ca, pe, ∅
    simp only [FLPg.empty]
    iframe
    iapply BigSepM2.bigSepM2_empty
    iempintro
  ipureintro
  refine ⟨fun id => ?_, ?_⟩
  · simp [FLPg.allIds, FLPg.pendingIds, FLPg.empty]
  · refine ⟨?_, ?_, List.Pairwise.nil, ?_, ?_⟩ <;>
      simp [FLPg.allIds, FLPg.pendingIds, FLPg.empty]

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
