/-
Proof of `Spec/go_etcd_io/etcd/client/v3/ChannelKeyFromContext.lean` (PR #21765).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ChannelKeyFromContext

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

theorem ChannelKeyFromContext.wp_proof
    (wp_channelKeyFromContext : channelKeyFromContext.spec (GF := GF) (hG := hG)) :
    ChannelKeyFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  wp_auto
  wp_apply wp_channelKeyFromContext ctx o $$ [$Hctx] as %key %ok %Hko
  iapply HΦ
  ipureintro; exact Hko.1

end proof

end EtcdGrove
end Perennial
