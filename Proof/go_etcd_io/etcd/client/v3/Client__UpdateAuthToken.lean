/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__UpdateAuthToken.lean` (PR etcd#21909). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__UpdateAuthToken

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.UpdateAuthToken.wp_proof : Client.UpdateAuthToken.spec (GF := GF) (hG := hG) := by
  intro c old token atb
  wp_start as ⟨Htok, #Hatb, #Hb⟩
  iunfold tokenBundleOk at Hb
  icases Hb with ⟨%ti, %Hti, #Hupd⟩
  subst Hti
  wp_auto
  wp_apply Hupd
  iapply HΦ
  iexact Htok

end proof

end EtcdGrove
end Perennial
