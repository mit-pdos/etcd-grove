/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Cmp__Clone.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.cloneCompare
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

theorem Cmp.Clone.wp_proof (wp_cloneCompare : cloneCompare.spec (GF := GF) (hG := hG)) :
    Cmp.Clone.spec (GF := GF) (hG := hG) := by
  intro cmpp c m dq
  wp_start as ⟨Hc, #Hat⟩
  unfold cmpAt
  icases Hat with ⟨%Hnn, #Hp⟩
  ihave %Hcn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  wp_auto
  simp only [Hnn, decide_false]
  wp_auto
  wp_apply wp_cloneCompare $$ [$Hp] as %p' ⟨%Hnn', Hown⟩
  · iframe %
  iapply HΦ
  iframe Hown
  isplitl [c]
  · iapply typedPointsto_combine _ _ _ Hcn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro; exact Hnn'

end proof

end EtcdGrove
end Perennial
