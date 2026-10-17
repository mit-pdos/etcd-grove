/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/ReadConfStateFromBackend.lean`
(etcd-io/etcd#19693; pr-verify, 2026-10-17). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.ReadConfStateFromBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeConfStateFromBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.ReadConfStateFromBackend.wp_proof
    (hU : schema.UnsafeConfStateFromBackend.spec (GF := GF) (hG := hG)) :
    schema.ReadConfStateFromBackend.spec (GF := GF) (hG := hG) := by
  intro lg rt
  wp_start as #Hrt
  unfold csReadTx
  icases Hrt with ⟨#HRLock, #HRUnlock, #Hrd⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply HRLock
  wp_apply hU $$ [] as %cs Hcs
  · iframe #
  wp_apply HRUnlock
  iapply HΦ
  iexact Hcs

end proof

end EtcdGrove
end Perennial
