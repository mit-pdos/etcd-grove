/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeDeleteBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDeleteBucket
public import Spec.go_etcd_io.bbolt.Tx__DeleteBucket_kv
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

theorem backend.batchTx.UnsafeDeleteBucket.wp_proof
    (hDelBkt : bbolt.Tx.DeleteBucket_kv.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeDeleteBucket.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t st bk bi
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk⟩
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  icases Hei with ⟨%e, #He, %Hel⟩
  obtain ⟨Hptr, Hleaf, HIs⟩ := Hel
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
  wp_apply (hDelBkt st.tx γ.db st.C st.S ns bi.name DFrac.discard) $$ [$Hwtx $Hns]
    as %err ⟨-, Hr⟩
  icases Hr with (⟨%Hn, Hwtx, #Herr⟩ | ⟨%Hn, Hwtx⟩)
  · icombine He Herr gives %Heq
    subst Heq
    wp_auto
    wp_apply (_root_.Perennial.errors.wp_Is_leaf e (GoInterface.ok e) Hleaf HIs
      (fun tii h => by cases h; exact Hptr)
      (fun ii tii h1 h2 _ => by cases h1; cases h2; obtain ⟨_, l, _, hl⟩ := Hptr; exact ⟨l, hl⟩))
    iapply HΦ
    unfold BSess.delBucket
    rw [GMap.delete_notin _ _ Hn]
    iframe
  · obtain ⟨Hn, Herr⟩ := Hn
    subst Herr
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
