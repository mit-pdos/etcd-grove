/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Delete.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Delete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__delete
public import Spec.go_etcd_io.etcd.client.v3.OpDelete

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

theorem leasingKV.Delete.wp_proof
    (hDel : EtcdGrove.OpDelete.spec (GF := GF) (hG := hG))
    (hdel : leasingKV.delete.spec (GF := GF) (hG := hG)) :
    leasingKV.Delete.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key sl gs lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hcc, #Hopts, #Hlo, %Hnp⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply hDel key sl gs $$ [$Hcv $Hopts] as %opv #Hop
  · ipureintro; exact Hnp.1
  wp_apply (hdel lkv γ pfx ctx cs opv (opDeleteModel key gs) lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
    as %dr %err H
  · ipureintro; exact Hnp.2
  iapply HΦ $$ H

end proof

end leasing
end EtcdGrove
end Perennial
