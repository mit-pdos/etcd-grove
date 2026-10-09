/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__Ctx.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.Ctx.wp_proof : Client.Ctx.spec (GF := GF) (hG := hG) := by
  intro cl c
  wp_start as #Hc
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
