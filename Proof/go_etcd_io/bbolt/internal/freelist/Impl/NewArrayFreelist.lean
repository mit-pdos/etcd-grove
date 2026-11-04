/-
`NewArrayFreelist()` (U2 internal): a fresh, empty array freelist with no reader.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.newShared
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Open

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

abbrev NewArrayFreelist.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist }}
    (App (Val #(functions go_etcd_io.bbolt.internal.freelist.NewArrayFreelist [])) (Val #()))
  {{ (fli : GoInterface), RET #fli; ⌜fli ≠ interface.nil⌝ ∗ flPgOwn fli FLPg.empty ∗
      flRoOwn fli [] }}

theorem NewArrayFreelist.wp_proof : NewArrayFreelist.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply newShared.wp_proof as %s ⟨Hsh, Hro⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %slp ⟨Hsl, Hslcap⟩
  wp_auto
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  iunfold ownShC at Hsh
  iNamed Hsh
  dsimp only
  iStructNamed «$r0»
  ipersist shared
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; simp
  isplitr [Hro]
  · iapply (flPgOwn_close (arrayImpl «$r0_ptr») «$r0_ptr» s
      (interface.mkOk (go.GoType.PointerType array'.ty) #«$r0_ptr») FLPg.empty (Or.inl rfl) rfl)
    dsimp only [arrayImpl]
    iframe
    isplitl []
    · iexact shared
    isplitl [Hsl]
    · iExactEq Hsl; rfl
    iunfold ownSh
    iexists c
    iunfold ownShC
    iframe
    ipureintro; exact Hok
  · iunfold flRoOwn
    iexists «$r0_ptr», s, slice.nil
    iframe
    isplitl []
    · iunfold flImplAt; ileft; isplit
      · ipureintro; rfl
      · iexact shared
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
