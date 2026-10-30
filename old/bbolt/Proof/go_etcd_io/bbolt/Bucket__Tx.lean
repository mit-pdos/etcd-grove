module
public import Spec.go_etcd_io.bbolt.Bucket__Tx

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

theorem Bucket.Tx.wp_proof  :
    Bucket.Tx.spec (GF := GF) (hG := hG) := by
  intro bl V q
  wp_start as HR
  isimp only [bktR, bktCtx] at HR
  icases HR with ⟨⟨%bv, %ib, %t, %dbl, Hbk, Hib, Ht, Hdata, Hps, %Hcx⟩, Hpgs, He, %Hok⟩
  have Hbtx : bv.tx' = V.tx := Hcx.2.2.2.2.2.2.2.1
  have Hbv : bv = V.bkt := Hcx.2.2.2.2.2.2.2.2.1
  have Htv : t = V.txv := Hcx.2.2.2.2.2.2.2.2.2.1
  have Hsq : ib.sequence' = V.seq := Hcx.2.2.2.2.2.2.2.2.2.2
  wp_auto
  ihave HR : bktR bl V q $$ [Hbk Hib Ht Hdata Hps Hpgs He]
  · unfold bktR
    isplitl [Hbk Hib Ht Hdata Hps]
    · unfold bktCtx; iexists bv, ib, t, dbl; iframe; ipureintro; exact Hcx
    iframe; ipureintro; exact Hok
  rw [Hbtx]
  iapply HΦ
  iframe


end proof

end bbolt
end EtcdGrove
end Perennial
