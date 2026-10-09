/-
Proof of `Spec/consistentIndex__ConsistentApplyingIndex.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.Spec.consistentIndex__ConsistentApplyingIndex

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.ConsistentApplyingIndex.wp_proof :
    consistentIndex.ConsistentApplyingIndex.spec (GF := GF) (hG := hG) := by
  intro ci a t
  wp_start as Happ
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  unfold ciApplying
  icases Happ with ⟨Ha, Ht⟩
  wp_auto
  wp_apply wp_LoadUint64_own $$ [$Ha] as Ha
  wp_apply wp_LoadUint64_own $$ [$Ht] as Ht
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
