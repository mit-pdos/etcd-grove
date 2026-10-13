module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree
public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas

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

theorem adt.NewIntervalTree.wp_proof : adt.NewIntervalTree.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  rename_i s
  irename «$r0» => Hs
  wp_alloc t as Ht
  wp_auto
  iapply HΦ
  unfold adt.ownIvt
  iexists _, .leaf
  iframe Ht
  simp only
  isplitl [Hs]
  · unfold adt.ownSentinel; iexists _; iexact Hs
  isplitl []
  · rw [adt.ownNode_leaf]; ipureintro; rfl
  ipureintro
  exact ⟨rfl, adt.rbOk_leaf, List.Pairwise.nil, rfl, by simp⟩

end proof

end EtcdGrove
end Perennial
