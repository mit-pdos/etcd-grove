module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__createIntervalNode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.createIntervalNode.wp_proof :
    adt.intervalTree.createIntervalNode.spec (GF := GF) (hG := hG) := by
  intro K hK t s dq vb ve b e v
  wp_start as ⟨Hs, #Hb, #He⟩
  wp_auto
  wp_alloc z as Hz
  ihave %Hzn := typedPointsto_not_null _ _ _ $$ Hz
  iStructNamed Hz
  wp_auto
  iapply HΦ
  simp only [adt.colorW]
  iframe Hs left right parent c
  isplitl []
  · ipureintro; exact Hzn
  isplitl [iv]
  · iapply K.ivAt_intro _ _ _ vb ve
    iframe ∗ #
  iapply K.maxAt_intro _ _ _ ve
  iframe ∗ #

end proof

end EtcdGrove
end Perennial
