/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/concurrentReadTx__Lock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__Lock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.concurrentReadTx.Lock.wp_proof :
    backend.concurrentReadTx.Lock.spec (GF := GF) (hG := hG) := by
  intro crt
  wp_start
  wp_auto
  iapply HΦ
  itrivial


end proof

end EtcdGrove
end Perennial
