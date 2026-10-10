/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Get.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Get
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__get
public import Spec.go_etcd_io.etcd.client.v3.OpGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.Get.wp_proof
    (hOpGet : EtcdGrove.OpGet.spec (GF := GF) (hG := hG))
    (hget : leasingKV.get.spec (GF := GF) (hG := hG)) :
    leasingKV.Get.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key sl gs lo q
  wp_start as ⟨#Hlkv, Hrd, Hslot, #Hctx, #Hopts, #Hlo, %Hgs, Hopen, Htok⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hOpGet key sl gs $$ [$Hcv $Hopts] as %opv #Hop
  · ipureintro; exact Hgs.1
  wp_apply hget lkv γ pfx ctx cs opv (opGetModel key gs) lo q
    $$ [$Hpkg $Hlkv $Hrd $Hslot $Hctx $Hop $Hlo $Hopen $Htok] as %ret %err H
  · ipureintro; exact Hgs.2
  iapply HΦ
  iexact H

end proof

end leasing
end EtcdGrove
end Perennial
