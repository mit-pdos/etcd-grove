/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeCreateBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeCreateBucket
public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists_kv
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

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

theorem backend.batchTx.UnsafeCreateBucket.wp_proof
    (hCreate : bbolt.Tx.CreateBucketIfNotExists_kv.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeCreateBucket.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t st bk bi Hn0 Hn1
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, %Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  unfold btW
  icases Hw with ⟨Htx, Hpend, Hwtx⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %Hbo, #-, #HName, #-⟩
  subst Hbo
  wp_auto
  wp_apply HName as %ns #Hns
  wp_apply (hCreate st.tx γ.db st.C st.S ns bi.name DFrac.discard Hn0 Hn1) $$ [$Hwtx $Hns]
    as %bkt %err ⟨%Herr, Hwtx, -, -⟩
  subst Herr
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
