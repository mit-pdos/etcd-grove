/-
The lessor's proofs' lemmas (2026-10-13, unit 8). Lean-first (no Rocq counterpart).

A `LeaseItem` is a safe map key (comparing it with itself does not panic: a struct of a
string).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

instance leaseItem_safeMapKey (k : LeaseItem) : SafeMapKey (GF := GF) LeaseItem.ty k where
  wp_go_eq_safe_map_key s E Φ := by
    iintro HΦ
    wp_pures
    iapply HΦ

end lemmas

end lease
end EtcdGrove
end Perennial
