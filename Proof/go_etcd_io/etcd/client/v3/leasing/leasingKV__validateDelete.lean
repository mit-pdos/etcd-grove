/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__validateDelete.lean` (etcd#22118).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__validateDelete
public import Spec.go_etcd_io.etcd.client.v3.Op__IsDelete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteIntersectsLeasingPrefix
public import Spec.google_golang_org.grpc.status.Errorf

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

theorem leasingKV.validateDelete.wp_proof
    (hIsDel : EtcdGrove.Op.IsDelete.spec (GF := GF) (hG := hG))
    (hInt : leasingKV.deleteIntersectsLeasingPrefix.spec (GF := GF) (hG := hG))
    (hErrf : status.Errorf.spec (GF := GF) (hG := hG)) :
    leasingKV.validateDelete.spec (GF := GF) (hG := hG) := by
  intro lkv pfx opv o
  wp_start as ⟨#Hpfx, #Hop⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hIsDel $$ [$Hcv $op $Hop] as op
  wp_if_destruct
  · (try wp_auto)
    wp_apply hInt $$ [$Hpfx $Hop]
    cases hi : leaseDelIntersects pfx o
    · (try wp_auto)
      iapply HΦ
      ipureintro
      simp [leaseDelRejected, hi]
    · (try wp_auto)
      wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #pfx]
      isplitr
      · ipureintro; rfl
      iintro %sla -
      (try wp_auto)
      wp_apply (hErrf (W32 3)) $$ [$Hst] as %e2 %He2
      · ipureintro
        simp only [google_golang_org.grpc.codes.OK]
        exact fun h => absurd (go.intoVal_inj h) (by decide)
      (try wp_auto)
      iapply HΦ
      ipureintro
      simp [leaseDelRejected, hi, *]
  · (try wp_auto)
    iapply HΦ
    ipureintro
    simp_all [leaseDelRejected]

end proof

end leasing
end EtcdGrove
end Perennial
