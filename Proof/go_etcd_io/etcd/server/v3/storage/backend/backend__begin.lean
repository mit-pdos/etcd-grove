/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__begin.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import Spec.go_etcd_io.bbolt.Tx__Size_kv
public import Spec.go_etcd_io.bbolt.Tx__DB_kv
public import Spec.go_etcd_io.bbolt.DB__Stats_kv
public import Spec.go_etcd_io.bbolt.DB__Info_kv
public import GeneratedProof.go_etcd_io.bbolt

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

theorem backend.backend.begin.wp_proof
    (hUB : backend.backend.unsafeBegin.spec (GF := GF) (hG := hG))
    (hSize : bbolt.Tx.Size_kv.spec (GF := GF) (hG := hG))
    (hDB : bbolt.Tx.DB_kv.spec (GF := GF) (hG := hG))
    (hStats : bbolt.DB.Stats_kv.spec (GF := GF) (hG := hG))
    (hInfo : bbolt.DB.Info_kv.spec (GF := GF) (hG := hG)) :
    backend.backend.begin.spec (GF := GF) (hG := hG) := by
  intro γ P WR b db D w
  wp_start as ⟨#Hb, Hmu, Hown, Hwr⟩
  icases isBackend_b γ P WR b $$ Hb with
    ⟨%t, %rt, %db0, %lg, #-, #-, #Hlg, %Hlgn, #Hmi, #-⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hmu] as ⟨Hrl, >Hdbp⟩
  wp_apply (hUB γ P WR b db sync.rfrac D w) $$ [$Hdbp $Hown $Hwr] as %tx ⟨Hdbp, Hown, #Hisdb, #Htxdb, Htx⟩
  · iframe #
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hdbp] as Hmu
  · inext; iexact Hdbp
  ihave Hl : (txLive tx 1 ∗ (txLive tx 1 -∗ (if w then ownWTx tx γ.db D D else
      iprop(txLive tx 1 ∗ rtxSnap tx D ∗ rtxStats tx)))) $$ [Htx]
  · cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Htx with ⟨Hl, Hs, Hst⟩
      iframe Hl
      iintro Hl
      iframe
    · simp only [↓reduceIte]
      iapply ownWTx_live $$ Htx
  icases Hl with ⟨Hlive, Hback⟩
  wp_apply (hSize tx 1) $$ [$Hlive] as %sz Hlive
  wp_apply (hDB tx db 1) $$ [$Hlive $Htxdb] as Hlive
  wp_apply (hStats db) $$ [$Hisdb] as %stats -
  wp_apply (wp_metricStore b go!"size" sz (by simp)) $$ [$Hmi]
  wp_apply (hInfo db) $$ [$Hisdb] as %i ⟨%iv, #Hi⟩
  iStructNamed Hi
  wp_auto
  wp_apply (wp_metricStore b go!"sizeInUse" _ (by simp)) $$ [$Hmi]
  wp_apply (wp_metricStore b go!"openReadTxN" _ (by simp)) $$ [$Hmi]
  iapply HΦ
  ispecialize Hback $$ Hlive
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
