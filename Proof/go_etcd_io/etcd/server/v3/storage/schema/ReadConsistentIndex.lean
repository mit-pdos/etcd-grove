/-
Proof of `Spec/schema_ReadConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.ReadConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.ReadConsistentIndex.wp_proof
    (hR : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG)) :
    schema.ReadConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro rt E View
  wp_start as #Hrt
  unfold metaReadTx
  icases Hrt with ⟨#HRLock, #HRUnlock, #Hrd⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply HRLock
  wp_apply_core (hR rt E View (fun _ => iprop(True))) $$ [] [HΦ defer]
  · iframe Hpkg Hrd
  iapply readCIAU_A
  iapply readCIAU_wand $$ HΦ
  iintro %m Hm
  wp_auto
  wp_apply HRUnlock
  iexact Hm

end proof

end EtcdGrove
end Perennial
