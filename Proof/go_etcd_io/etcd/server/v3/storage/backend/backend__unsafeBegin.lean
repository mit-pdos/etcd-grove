/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/backend__unsafeBegin.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__unsafeBegin
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.DB__Begin

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
`_kv` spec `DB.Begin_kv`). -/
private theorem bbolt.kvGlue_DB__Begin_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Begin.spec (GF := GF) (hG := hG)) :
  ∀ (db : Loc) (γ : DBNames) (D : backend.Data) (w : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ (if w then wrTok γ else threadTok) }}
    (App (Val (db @!! go.GoType.PointerType go_etcd_io.bbolt.DB.ty @!! go!"Begin")) (Val #w))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err); ownDB db γ D ∗ isDB db γ ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ (if w then wrTok γ else threadTok)) ∨
       (⌜err = GoInterface.nil⌝ ∗ backend.txDB tx γ db ∗
        (if w then ownWTx tx γ D D else txLive tx γ 1 (bbolt.TxView.ro D)))) }} := by
  intro db γ D w
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.ownDB, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.ownWTx, backend.ownWTxG,
      backend.txDB, onFs_some hfs]
    cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      iintro %Φ ⟨-, ⟨#Hdb, Hs, Hrest⟩, Htok⟩ HΦ
    · ihave Hau := backend.boltState_read_au_q γ (1 : Qp).half D $$ Hs
      have h' := h db γ false (fun D' => iprop(bbolt.boltState γ (1 : Qp).half D ∗ ⌜D' = D⌝))
      simp only [Bool.false_eq_true, ↓reduceIte] at h'
      iapply wp_fupd
      wp_apply h' $$ [$Hdb $Htok $Hau] as %tx %err Hr
      icases Hr with (⟨%He, #Htd, %D', Htx, Hs, %HD⟩ | ⟨%He, -, Htok, Hau⟩)
      · subst HD
        imodintro
        iapply HΦ; iframe Hs Hdb Hrest
        iright; isplitr; · ipureintro; exact He
        iframe Htd Htx
      · imod (backend.boltState_au_back_q γ (1 : Qp).half D) $$ Hau with Hs
        imodintro
        iapply HΦ; iframe Hs Hdb Hrest
        ileft; iframe Htok; ipureintro; exact He.1
    · have h' := h db γ true (fun _ => iprop(emp))
      simp only [↓reduceIte] at h'
      wp_apply h' $$ [$Hdb] as %tx %err Hr
      icases Hr with (⟨%He, #Htd, %D', Htx⟩ | ⟨%He, -, -⟩)
      · icases persistent_entails_right (bbolt.boltTx_base tx γ 1 (1 : Qp).half (TxView.wr D') D) $$ [Htx Hs]
          with ⟨%Hb, Htx, Hs⟩
        · iframe Htx Hs
        have HD : D' = D := Hb rfl
        subst HD
        iapply HΦ; iframe Hs Hdb Hrest
        iright; isplitr; · ipureintro; exact He
        iframe Htd
        iexists (fun _ => 0)
        rw [← wView_wr]
        iexact Htx
      · iapply HΦ; iframe Hs Hdb Hrest
        ileft; unfold wrTok; isplitr; · ipureintro; exact He.1
        itrivial

theorem backend.backend.unsafeBegin.wp_proof
    (hBegin : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.DB.Begin.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.backend.unsafeBegin.spec (GF := GF) (hG := hG) := by
  replace hBegin := bbolt.kvGlue_DB__Begin_kv hBegin
  intro γd b db q D w
  wp_start as ⟨#Hb, Hdb, Hown, Hwr⟩
  unfold beginCtx
  icases Hb with ⟨%lg, #Hlg, #Hlgn, #-⟩
  wp_auto
  wp_apply (hBegin db γd D w) $$ [$Hown $Hwr] as %tx %err ⟨Hown, #Hisdb, Hr⟩
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, #Htxdb, Htx⟩)
  · rcases err with ei | _
    · wp_auto
      wp_apply hError as %f -
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      try iintro %_ ⟨_, -⟩
      try wp_auto
      wp_apply hFatal lg $$ [] as %v Hf
      · iexact Hlgn
      iexfalso
      iexact Hf
    · exact absurd rfl Herr
  · subst Herr
    wp_auto
    iapply HΦ
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
