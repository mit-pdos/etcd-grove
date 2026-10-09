/-
Proof of `Spec/go_etcd_io/etcd/client/v3/cloneCompare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.cloneCompare
public import Spec.google_golang_org.protobuf.proto.Clone
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem cloneCompare.wp_proof (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG)) :
    cloneCompare.spec (GF := GF) (hG := hG) := by
  intro p m
  wp_start as ⟨#Hp, %Hnn⟩
  wp_auto
  simp only [Hnn, decide_false]
  wp_auto
  wp_apply wp_Clone $$ [$Hp] as %p' ⟨%Hnn', Hown⟩
  · iframe %
  iapply HΦ
  iframe
  ipureintro; exact Hnn'

end proof

end EtcdGrove
end Perennial
