/-
Proof of `Spec/go_etcd_io/etcd/client/v3/withMax.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.withMax

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem withMax.wp_proof :
    withMax.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  wp_auto
  ipersist maxRetries
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold optApplyOk
  iintro !> %o %ov
  wp_start as ⟨Ho, #Hok⟩
  wp_auto
  iapply HΦ
  iexists _
  iframe
  unfold optionsOk at *
  iexact Hok

end proof

end EtcdGrove
end Perennial
