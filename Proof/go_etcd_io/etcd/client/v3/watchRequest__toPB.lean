/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchRequest__toPB.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchRequest__toPB

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem watchRequest.toPB.wp_proof : watchRequest.toPB.spec (GF := GF) (hG := hG) := by
  intro wr key ed rv pn flt dq sr bd
  wp_start as ⟨#Hk, #He, Hrv, #Hpn, #Hflt, #Hfs, #Hpkv, #Hfr⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_string_to_bytes key as %ksl ⟨Hks, -⟩
  wp_apply wp_string_to_bytes ed as %esl ⟨Hes, -⟩
  rename_i cr ow
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  irename : (ow ↦ (_ : etcdserverpb.WatchRequest_CreateRequest) : IProp GF) => How
  irename : (cr ↦ (_ : etcdserverpb.WatchCreateRequest) : IProp GF) => Hcr
  ihave %Hcrn := typedPointsto_not_null _ _ _ $$ Hcr
  iStructNamed Hp
  iStructNamed How
  iStructNamed Hcr
  ipersist RequestUnion; ipersist CreateRequest
  ipersist Key; ipersist RangeEnd; ipersist StartRevision; ipersist ProgressNotify
  ipersist Filters; ipersist PrevKv; ipersist WatchId; ipersist Fragment
  ipersist Hks; ipersist Hes
  imodintro
  iapply HΦ
  iframe
  unfold v3rpc.watchReqSend v3rpc.oneofCreate v3rpc.createReqSend
  iexists _
  iframe #
  iexists cr
  isplitl []
  · iexists ow
    iframe #
    ipureintro; rfl
  isplitl []
  · ipureintro; exact Hcrn
  iexists ksl, esl, flt
  simp only [createOf]
  iframe #
  rw [show (W64 0 : w64) = 0 from rfl]
  iexact WatchId

end proof

end EtcdGrove
end Perennial
