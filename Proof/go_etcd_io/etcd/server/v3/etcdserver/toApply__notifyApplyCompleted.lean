/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/toApply__notifyApplyCompleted.lean`. Lean-first
(no Rocq counterpart; etcd-io/etcd#22223).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.toApply__notifyApplyCompleted

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem toApply.notifyApplyCompleted.wp_proof :
    toApply.notifyApplyCompleted.spec (GF := GF) (hG := hG) := by
  intro ap f acc P
  wp_start as ⟨#Hf, #Hfok, HP, #Hacc, Hdone⟩
  (try wp_auto)
  iunfold onApplyOk at Hfok
  iunfold applyDoneOk at Hdone
  -- `if ap.applyCompletedC != nil { close(ap.applyCompletedC) }`, then return
  -- `if ap.onApplyCompleted != nil { ap.onApplyCompleted() }`
  wp_if_destruct
  · -- nil: no call
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      itrivial
    · icases Hdone with (%Han | ⟨%γc, Hdone⟩)
      · exact absurd Han (by assumption)
      wp_apply wp_broadcast_chan_close acc γc iprop(True) $$ [$Hdone] as -
      · itrivial
      (try wp_auto)
      iapply HΦ
      itrivial
  · icases Hfok with (%Hfn | #Hft)
    · exact absurd Hfn Hif
    wp_bind (App (Val #f) (Val #()))
    iapply Hft $$ HP
    inext
    iintro -
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      itrivial
    · icases Hdone with (%Han | ⟨%γc, Hdone⟩)
      · exact absurd Han (by assumption)
      wp_apply wp_broadcast_chan_close acc γc iprop(True) $$ [$Hdone] as -
      · itrivial
      (try wp_auto)
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
