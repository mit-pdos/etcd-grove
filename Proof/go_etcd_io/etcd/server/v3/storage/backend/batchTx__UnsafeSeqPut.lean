/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeSeqPut.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeSeqPut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__unsafePut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

theorem backend.batchTx.UnsafeSeqPut.wp_proof
    (hup : backend.batchTx.unsafePut.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeSeqPut.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t st bk bi key value kb vb dk Hk0 Hk1 Hv
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey, #Hval⟩
  wp_auto
  wp_apply (hup γ P W Pk b t st bk bi key value kb vb dk true Hk0 Hk1 Hv) $$ [$Hw $Hkey] as ⟨Hw, Hkey⟩
  · iframe #
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
