/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewKVClient.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewKVClient

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

theorem NewKVClient.wp_proof : NewKVClient.spec (GF := GF) (hG := hG) := by
  intro cc
  wp_start
  wp_auto
  wp_alloc kc as Hkc
  iStructNamed Hkc
  ipersist cc
  wp_auto
  iapply HΦ
  iexists kc
  iframe
  isplitl []
  · ipureintro; rfl
  · iexact cc

end proof

end EtcdGrove
end Perennial
