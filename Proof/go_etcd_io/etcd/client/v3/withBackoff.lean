/-
Proof of `Spec/go_etcd_io/etcd/client/v3/withBackoff.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.withBackoff

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

theorem withBackoff.wp_proof :
    withBackoff.spec (GF := GF) (hG := hG) := by
  intro bf
  wp_start as #Hbf
  wp_auto
  ipersist bf
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold optApplyMax
  iintro !> %o %ov
  wp_start as ⟨Ho, #Hok⟩
  wp_auto
  iapply HΦ
  iexists _
  iframe
  isplitr
  · unfold optionsOk
    iexact Hbf
  ipureintro; exact ⟨rfl, fun _ => rfl⟩

end proof

end EtcdGrove
end Perennial
