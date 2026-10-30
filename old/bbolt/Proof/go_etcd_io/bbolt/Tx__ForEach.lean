module
public import Spec.go_etcd_io.bbolt.Tx__ForEach
public import Spec.go_etcd_io.bbolt.Bucket__ForEach

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

theorem Tx.ForEach.wp_proof (hForEach : Bucket.ForEach.spec (GF := GF) (hG := hG))
    (hBucket : Bucket.Bucket.spec (GF := GF) (hG := hG)) :
    Tx.ForEach.spec (GF := GF) (hG := hG) := by
  intro txl V q fn I Hbm Hwr
  wp_start as ⟨HR, Hst, HI, #Hfn⟩
  isimp only [txForEachFn] at Hfn
  wp_auto
  ipersist tx
  ipersist fn
  rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
    fun x b => by rw [go.intoVal_unfold GoFunc]]
  icases (bktR_split' _ V q.half q.half q (Qp.half_add_half q).symm).1 $$ HR with ⟨HRa, HRb⟩
  wp_apply hForEach _ V q.half _ iprop(I ∗ bktR (structFieldRef Tx go!"root" txl) V q.half)
    $$ [HRa Hst HI HRb] as %err ⟨HRa, Hst, HI, HRb⟩
  · iframe
    imodintro
    unfold forEachFn
    iintro %k %v %kb %vb %dq
    wp_start as ⟨⟨HI, HRb⟩, Hst, Hk, Hv, %Hel⟩
    wp_auto
    wp_apply hBucket _ V q.half k kb dq Hbm Hwr $$ [HRb Hst Hk] as %cl ⟨Hst, Hk, Hpost⟩
    · iframe
    try wp_auto
    icases Hpost with (⟨%Hcl, HRb⟩ | ⟨%V', %qc, %Hnest, HRb, HRc, Hback⟩)
    · wp_apply Hfn $$ %k %kb %dq %cl %V %q [HI Hst Hk] as %e ⟨HI, Hst, Hk, -⟩
      · iframe; ileft; ipureintro; exact Hcl
      iapply HΦ
      iframe
    · icases bktR_ne_null _ _ _ $$ HRc with ⟨%Hcn, HRc⟩
      wp_apply Hfn $$ %k %kb %dq %cl %V' %qc [HI Hst Hk HRc] as %e ⟨HI, Hst, Hk, Hc⟩
      · iframe; iright; iframe; ipureintro; exact Hnest
      icases Hc with (%Hc | HRc)
      · exact absurd Hc Hcn
      ihave HRb2 := Hback $$ HRc
      ihave HRb := (bktR_split' _ V q.half.half q.half.half q.half (Qp.half_add_half q.half).symm).2
        $$ [HRb HRb2]
      · iframe
      iapply HΦ
      iframe
  ihave HR := (bktR_split' _ V q.half q.half q (Qp.half_add_half q).symm).2 $$ [HRa HRb]
  · iframe
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
