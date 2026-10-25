/-
Proof of `Spec/go_etcd_io/etcd/client/v3/channelKeyForRequest.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.channelKeyForRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem channelKeyForRequest.wp_proof
    (wp_ChannelKeyFromContext : ChannelKeyFromContext.spec (GF := GF) (hG := hG)) :
    channelKeyForRequest.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  wp_auto
  wp_apply wp_ChannelKeyFromContext ctx o $$ [$Hctx] as %key %Hk
  subst Hk
  wp_if_destruct
  · iapply HΦ
    ipureintro
    simp [clientv3.reqChannelKey, Hif]
  · have h1 := Hif
    wp_if_destruct
    · iapply HΦ
      ipureintro
      simp [clientv3.reqChannelKey, Hif]
    · iapply HΦ
      ipureintro
      simp [clientv3.reqChannelKey, h1, Hif]

end proof

end EtcdGrove
end Perennial
