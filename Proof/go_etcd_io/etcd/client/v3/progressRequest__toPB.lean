/-
Proof of `Spec/go_etcd_io/etcd/client/v3/progressRequest__toPB.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.progressRequest__toPB

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem progressRequest.toPB.wp_proof : progressRequest.toPB.spec (GF := GF) (hG := hG) := by
  intro pr
  wp_start
  iapply wp_fupd
  wp_auto
  rename_i cr
  irename «$r0» => How
  irename : (cr ↦ zero_val etcdserverpb.WatchProgressRequest : IProp GF) => Hcr
  wp_alloc p as Hp
  ihave %Hcrn := typedPointsto_not_null _ _ _ $$ Hcr
  iStructNamed Hp
  iStructNamed How
  ipersist RequestUnion; ipersist ProgressRequest
  wp_auto
  imodintro
  iapply HΦ
  unfold v3rpc.watchReqSend v3rpc.oneofProgress
  iexists _
  iframe #
  iexists cr
  isplitl []
  · ipureintro; exact Hcrn
  iexists «$r0_ptr»
  iframe #
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
