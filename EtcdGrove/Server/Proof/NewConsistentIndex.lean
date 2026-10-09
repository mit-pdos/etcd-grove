/-
Proof of `Spec/NewConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Server.Spec.NewConsistentIndex

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

theorem NewConsistentIndex.wp_proof :
    NewConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro be
  wp_start
  wp_auto
  wp_alloc ci as Hci
  iStructNamed Hci
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γi, Hg⟩
  icases ghostVar_split γi (W64 0) (1 : Qp).half (1 : Qp).half $$ [Hg] with ⟨Hg1, Hg2⟩
  · rw [Qp.half_add_half]; iexact Hg
  imod inv_alloc ciN ⊤ (ciInv (hG := hG) ci ⟨γi⟩) $$ [consistentIndex term Hg2] with #Hinv
  · inext
    iunfold ciInv
    iexists (W64 0), (W64 0)
    iframe
  ihave ⟨Hbe1, Hbe2⟩ := (ciBe_halves ci be).2 $$ be
  imod sync.init_Mutex (ciLockInv (hG := hG) ci) ⊤ (ciMutexAddr ci) $$ mutex [Hbe1] with #Hmu
  · inext; iunfold ciLockInv; iexists be; iexact Hbe1
  wp_auto
  iapply HΦ $$ %ci %(⟨γi⟩ : CINames)
  iunfold isCI
  iunfold ciIdx
  iunfold ciApplying
  iunfold ciOwner
  iframe Hinv Hmu Hg1 Hbe2
  iframe

end proof

end EtcdGrove
end Perennial
