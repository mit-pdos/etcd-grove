/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Put.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__Put
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__put
public import Spec.go_etcd_io.etcd.client.v3.OpPut

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

theorem leasingKV.Put.wp_proof
    (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG))
    (hput : leasingKV.put.spec (GF := GF) (hG := hG)) :
    leasingKV.Put.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs key val sl gs top lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hcc, #Hopts, #Hlo, %Hpre⟩
  obtain ⟨Hpan, Ht, Htop⟩ := Hpre
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply hPut key val sl gs $$ [$Hcv $Hopts] as %opv #Hop
  · ipureintro; exact Hpan
  (try wp_auto)
  wp_apply (hput lkv γ pfx ctx cs opv (opPutModel key val gs) top lo)
    $$ [$Hpkg $Hlkv $Hrd $Hctx $Hcc $Hop $Hlo] as %pr %err Hres
  · ipureintro; exact ⟨Ht, Htop⟩
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end leasing
end EtcdGrove
end Perennial
