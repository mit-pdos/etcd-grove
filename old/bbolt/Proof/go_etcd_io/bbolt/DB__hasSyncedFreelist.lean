module
public import Spec.go_etcd_io.bbolt.DB__hasSyncedFreelist
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Freelist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.hasSyncedFreelist.wp_proof (hmeta : DB.meta.spec (GF := GF) (hG := hG))
    (hFreelist : Meta.Freelist.spec (GF := GF) (hG := hG)) :
    DB.hasSyncedFreelist.spec (GF := GF) (hG := hG) := by
  intro dbl m0 m1 dq dq0 dq1 v0 v1 Hc0 Hc1 Hval
  wp_start as ⟨Hf0, Hf1, H0, H1⟩
  wp_auto
  wp_apply hmeta dbl m0 m1 dq dq0 dq1 v0 v1 Hc0 Hc1 Hval $$ [Hf0 Hf1 H0 H1]
    as ⟨%Hv, Hf0, Hf1, H0, H1⟩
  · iframe
  cases metaPick v0 v1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_apply hFreelist m0 v0 dq0 $$ [H0] as H0
    · iframe
    try wp_auto
    iapply HΦ; iframe
  · simp only [↓reduceIte]
    wp_apply hFreelist m1 v1 dq1 $$ [H1] as H1
    · iframe
    try wp_auto
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
