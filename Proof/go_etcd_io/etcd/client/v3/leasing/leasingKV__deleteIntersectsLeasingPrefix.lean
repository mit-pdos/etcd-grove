/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__deleteIntersectsLeasingPrefix.lean` (etcd#22118). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteIntersectsLeasingPrefix
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.GetPrefixRangeEnd
public import Spec.go_etcd_io.etcd.client.v3.leasing.inRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.deleteIntersectsLeasingPrefix.wp_proof
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hGPRE : EtcdGrove.GetPrefixRangeEnd.spec (GF := GF) (hG := hG))
    (hIn : inRange.spec (GF := GF) (hG := hG)) :
    leasingKV.deleteIntersectsLeasingPrefix.spec (GF := GF) (hG := hG) := by
  intro lkv pfx opv o
  wp_start as ⟨#Hpfx, #Hop⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hop' := Hop
  iunfold opFullAt at Hop'
  icases Hop' with ⟨#HopAt, -⟩
  wp_auto
  wp_apply hKey $$ [$Hcv $op $Hop] as %ksl ⟨op, #Hk⟩
  wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
  wp_apply hRange $$ [$Hcv $op $HopAt] as %esl ⟨op, #He⟩
  wp_apply wp_bytes_to_string esl o.base.rangeEnd DFrac.discard $$ [$He] as -
  (try wp_auto)
  wp_apply hGPRE $$ [$Hcv]
  (try wp_auto)
  wp_if_destruct
  · wp_apply hIn
    (try wp_auto)
    rw [show leaseInRange o.key pfx (prefixRangeEnd pfx) = leaseDelIntersects pfx o by
      simp [leaseDelIntersects, *]]
    iapply HΦ
    itrivial
  · wp_apply hIn
    cases h1 : leaseInRange o.key pfx (prefixRangeEnd pfx)
    · (try wp_auto)
      wp_apply hIn
      (try wp_auto)
      rw [show leaseInRange pfx o.key o.base.rangeEnd = leaseDelIntersects pfx o by
        simp [leaseDelIntersects, *]]
      iapply HΦ
      itrivial
    · (try wp_auto)
      rw [show true = leaseDelIntersects pfx o by simp [leaseDelIntersects, *]]
      iapply HΦ
      itrivial

end proof

end leasing
end EtcdGrove
end Perennial
