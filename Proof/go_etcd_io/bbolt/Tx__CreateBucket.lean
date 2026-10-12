module
public import Spec.go_etcd_io.bbolt.Tx__CreateBucket

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

theorem Tx.CreateBucket.wp_proof (hCB : Bucket.CreateBucket.spec (GF := GF) (hG := hG)) :
    Tx.CreateBucket.spec (GF := GF) (hG := hG) := by
  intro W txl T key kb dk
  wp_start as ⟨Hown, Hk⟩
  isimp only [ownWriteTx] at Hown
  icases Hown with ⟨HG, Hv, %Hok⟩
  have Hrl : (T.bs !! structFieldRef Tx go!"root" txl).isSome := Hok.2.2.2.2.2.2.2.1
  wp_auto
  wp_apply hCB W txl T _ key kb dk Hrl $$ [HG Hv Hk] as %rb %err %T' Hpost
  · unfold ownWriteTx; iframe; ipureintro; exact Hok
  iapply HΦ $$ Hpost

end proof

end bbolt
end EtcdGrove
end Perennial
