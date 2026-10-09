module
public import Spec.k8s_io.utils.third_party.forked.golang.btree.Less

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI Iris.ProofMode k8s_io.utils.third_party.forked.golang.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

theorem Less.wp_proof : Less.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ ltb hord hlt
  wp_start
  wp_pures
  rw [recv_eq_func_mk]
  iapply HΦ
  unfold isLess orderedOrder
  iintro %a %b %ka %kb
  wp_start_folded as ⟨%ha, %hb⟩
  subst ha hb
  haveI : go.IsGoStepPureDet (GoOp GoLt T) (PairV #a #b) #(ltb a b) :=
    (hlt a b).isGoStep_det_internal
  wp_auto
  iapply HΦ
  ipureintro; rfl

end proof

end btree
end EtcdGrove
end Perennial
