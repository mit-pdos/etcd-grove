/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeDeleteForCompaction.lean`
(etcd#21982): the body is `t.UnsafeDelete(bucketType, key)`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDeleteForCompaction
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDelete

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

theorem backend.batchTx.UnsafeDeleteForCompaction.wp_proof
    (hDel : backend.batchTx.UnsafeDelete.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeDeleteForCompaction.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key kb dk
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey⟩
  wp_auto
  wp_apply (hDel γ P W Pk b t st bk bi key kb dk) $$ [$Hw $Hkey] as ⟨Hw, Hkey⟩
  · iframe #
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
