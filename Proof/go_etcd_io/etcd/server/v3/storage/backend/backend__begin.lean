/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__begin.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import GeneratedProof.go_etcd_io.bbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Size
public import Spec.go_etcd_io.bbolt.Tx__DB
public import Spec.go_etcd_io.bbolt.DB__Stats
public import Spec.go_etcd_io.bbolt.DB__Info

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Size_kv`). -/
private theorem bbolt.kvGlue_Tx__Size_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Size.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ q T }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; txLive tx γ q T }} := by
  intro tx γ q T
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, H⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl⟩ HΦ
    have h' := h tx γ q T
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl] as %n ⟨Hl, -⟩
    iapply HΦ; iframe

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.DB_kv`). -/
private theorem bbolt.kvGlue_Tx__DB_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.DB.spec (GF := GF) (hG := hG)) :
  ∀ (tx db : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ q T ∗ backend.txDB tx γ db }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"DB")) (Val #()))
  {{ RET #db; txLive tx γ q T }} := by
  intro tx db γ q T
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, #Hd⟩ HΦ
    have h' := h tx db γ q T
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hd] as Hl
    iapply HΦ; iframe

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `DB.Stats_kv`). -/
private theorem bbolt.kvGlue_DB__Stats_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Stats.spec (GF := GF) (hG := hG)) :
  ∀ (db tx : Loc) (γ : DBNames) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ txLive tx γ 1 T }}
    (App (Val (db @!! go.GoType.PointerType go_etcd_io.bbolt.DB.ty @!! go!"Stats")) (Val #()))
  {{ (s : Stats), RET #s; txLive tx γ 1 T }} := by
  intro db tx γ T
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hb, Hl⟩ HΦ
    have h' := h db γ (some (tx, T))
    simp only [bbolt.statSlot.eq_2] at h'
    wp_apply h' $$ [$Hb $Hl] as %s Hl
    iapply HΦ; iexact Hl

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `DB.Info_kv`). -/
private theorem bbolt.kvGlue_DB__Info_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Info.spec (GF := GF) (hG := hG)) :
  ∀ (db tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ isDB db γ ∗ backend.txDB tx γ db ∗ txLive tx γ q T }}
    (App (Val (db @!! go.GoType.PointerType go_etcd_io.bbolt.DB.ty @!! go!"Info")) (Val #()))
  {{ (i : Loc), RET #i; (∃ v : Info, i ↦ v) ∗ txLive tx γ q T }} := by
  intro db tx γ q T
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hb, #Hd, Hl⟩ HΦ
    have h' := h db tx γ q T
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hb $Hd $Hl] as %i ⟨Hl, %v, Hi⟩
    iapply HΦ; iframe Hl; iexists v; iexact Hi

theorem backend.backend.begin.wp_proof
    (hUB : backend.backend.unsafeBegin.spec (GF := GF) (hG := hG))
    (hSize : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Size.spec (GF := GF) (hG := hG))
    (hDB : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.DB.spec (GF := GF) (hG := hG))
    (hStats : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Stats.spec (GF := GF) (hG := hG))
    (hInfo : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Info.spec (GF := GF) (hG := hG)) :
    backend.backend.begin.spec (GF := GF) (hG := hG) := by
  replace hSize := bbolt.kvGlue_Tx__Size_kv hSize
  replace hDB := bbolt.kvGlue_Tx__DB_kv hDB
  replace hStats := bbolt.kvGlue_DB__Stats_kv hStats
  replace hInfo := bbolt.kvGlue_DB__Info_kv hInfo
  intro γd b db D w
  wp_start as ⟨#Hb, Hmu, Hown, Hwr⟩
  ihave #Hc : beginCtx b $$ [Hb]
  · iexact Hb
  iunfold beginCtx at Hc
  icases Hc with ⟨%lg, #Hlg, #Hlgn, #Hmi⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RLock $$ [$Hmu] as ⟨Hrl, >Hdbp⟩
  wp_apply (hUB γd b db sync.rfrac D w) $$ [$Hdbp $Hown $Hwr] as %tx ⟨Hdbp, Hown, #Hisdb, #Htxdb, Htx⟩
  · iframe #
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hdbp] as Hmu
  · inext; iexact Hdbp
  ihave Hl : (∃ T, txLive tx γd 1 T ∗ (txLive tx γd 1 T -∗ (if w then ownWTx tx γd D D else
      txLive tx γd 1 (bbolt.TxView.ro D)))) $$ [Htx]
  · cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iexists (bbolt.TxView.ro D)
      iframe Htx
      iintro Hl
      iexact Hl
    · simp only [↓reduceIte]
      iapply ownWTx_live $$ Htx
  icases Hl with ⟨%T, Hlive, Hback⟩
  wp_apply (hSize tx γd 1 T) $$ [$Hlive] as %sz Hlive
  wp_apply (hDB tx db γd 1 T) $$ [$Hlive $Htxdb] as Hlive
  wp_apply (hStats db tx γd T) $$ [$Hisdb $Hlive] as %stats Hlive
  wp_apply (wp_metricStore b go!"size" sz (by simp)) $$ [$Hmi]
  wp_apply (hInfo db tx γd 1 T) $$ [$Hisdb $Htxdb $Hlive] as %i ⟨⟨%iv, Hi⟩, Hlive⟩
  iStructNamed Hi
  try wp_auto
  wp_apply (wp_metricStore b go!"sizeInUse" _ (by simp)) $$ [$Hmi]
  wp_apply (wp_metricStore b go!"openReadTxN" _ (by simp)) $$ [$Hmi]
  iapply HΦ
  ispecialize Hback $$ Hlive
  iframe
  iframe #

end proof

end EtcdGrove
end Perennial
