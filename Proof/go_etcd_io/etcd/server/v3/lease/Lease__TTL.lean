/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__TTL.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__TTL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.TTL.wp_proof : lease.Lease.TTL.spec (GF := GF) (hG := hG) := by
  intro l t dq
  wp_start as Ht
  wp_auto
  iapply HΦ $$ Ht

end proof

end EtcdGrove
end Perennial
