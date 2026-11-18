/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__commit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.time.Duration__Seconds
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Commit
public import Spec.go_etcd_io.bbolt.Tx__Stats

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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Commit_kv`). -/
private theorem bbolt.kvGlue_Tx__Commit_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Commit.spec (GF := GF) (hG := hG)) :
  ∀ (db tx : Loc) (γ : DBNames) (D S : backend.Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ backend.txDB tx γ db ∗ ownWTx tx γ D S }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err; backend.txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ ownDB db γ S ∗ wrTok γ) ∨ ⌜err ≠ GoInterface.nil⌝) }} := by
  intro db tx γ D S
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, ⟨#Hdb, Hs, Hrest⟩, #Hd, ⟨%G, Hl⟩⟩ HΦ
    ihave Hau := bbolt.boltState_commit_au γ D S $$ Hs
    have h' := h tx γ (wView D S G) (bbolt.boltState γ 1 S)
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hau] as %err ⟨#Hdn, Hr⟩
    all_goals try (ipureintro; first | trivial | rfl)
    iapply HΦ; iframe Hdn
    icases Hr with (⟨%He, Hs⟩ | ⟨%He, -⟩)
    · ileft; isplitr; · ipureintro; exact He
      iframe Hs Hdb Hrest
      unfold wrTok; itrivial
    · iright; ipureintro; exact He

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Stats_kv`). -/
private theorem bbolt.kvGlue_Tx__Stats_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Stats.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ backend.txDone tx }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Stats")) (Val #()))
  {{ (s : TxStats), RET #s; True }} := by
  intro tx
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, H⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hd⟩ HΦ
    have h' := h tx
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hd] as %s -
    iapply HΦ; itrivial

theorem backend.batchTx.commit.wp_proof
    (hCommit : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Commit.spec (GF := GF) (hG := hG))
    (hStats : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Stats.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.batchTx.commit.spec (GF := GF) (hG := hG) := by
  replace hCommit := bbolt.kvGlue_Tx__Commit_kv hCommit
  replace hStats := bbolt.kvGlue_Tx__Stats_kv hStats
  intro γ P W Pk b t db st stop
  wp_start as ⟨#Hb, #Ht, Hw, Hown, #Htxdb, Hmu⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, #Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db1, %lg', #-, #-, #-, #-, #Hmi, #-⟩
  ihave #Hbc := isBackend_beginCtx γ P W Pk b $$ Hb
  ihave Hi : (backendInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨⟨%h1, #Hg1, #Hs1⟩, ⟨%h2, #Hg2, #Hs2⟩, ⟨%h3, #Hg3, #Hs3⟩, ⟨%h4, #Hg4, #Hs4⟩, -⟩
  unfold histSpec
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  icases ownWTx_live st.tx γ.db st.C st.S $$ Hwtx with ⟨%Tw, Hlive, Hback⟩
  icases persistent_entails_right (txLive_nonnull st.tx γ.db 1 Tw) $$ Hlive with ⟨%Hnn, Hlive⟩
  ihave Hwtx := Hback $$ Hlive
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  by_cases hA : st.pend = W64 0 ∧ stop = false
  · obtain ⟨hA1, rfl⟩ := hA
    rw [hA1]
    wp_auto
    iapply HΦ
    iframe Hmu
    ileft
    iframe
    iframe #
    ipureintro
    exact ⟨rfl, rfl⟩
  have Hnot := hA
  wp_if_destruct
  · cases stop
    · exact absurd ⟨Hif, rfl⟩ hA
    try wp_auto
    wp_apply time.wp_Now as %start -
    wp_apply (hCommit db st.tx γ.db st.C st.S) $$ [$Hown $Htxdb $Hwtx] as %err ⟨#Hdone, Hr⟩
    wp_apply (hStats st.tx) $$ [$Hdone] as %s1 -
    wp_apply hSeconds as %f1 -
    wp_apply Hs1
    wp_apply (hStats st.tx) $$ [$Hdone] as %s2 -
    wp_apply hSeconds as %f2 -
    wp_apply Hs2
    wp_apply (hStats st.tx) $$ [$Hdone] as %s3 -
    wp_apply hSeconds as %f3 -
    wp_apply Hs3
    wp_apply time.wp_Since as %d -
    wp_apply hSeconds as %f4 -
    wp_apply Hs4
    wp_apply (wp_commitsAdd b (W64 1)) $$ [$Hmi] as %nc -
    icases Hr with (⟨%Herr, Hown, Hwr⟩ | %Herr)
    · subst Herr
      wp_auto
      try wp_auto
      iapply HΦ
      iframe Hmu
      iright
      iframe Hown Hpend
      isplitr
      · ipureintro; exact Hnot
      iexists _
      iframe Htxf
      simp only [↓reduceIte]
      itrivial
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
  · try wp_auto
    wp_apply time.wp_Now as %start -
    wp_apply (hCommit db st.tx γ.db st.C st.S) $$ [$Hown $Htxdb $Hwtx] as %err ⟨#Hdone, Hr⟩
    wp_apply (hStats st.tx) $$ [$Hdone] as %s1 -
    wp_apply hSeconds as %f1 -
    wp_apply Hs1
    wp_apply (hStats st.tx) $$ [$Hdone] as %s2 -
    wp_apply hSeconds as %f2 -
    wp_apply Hs2
    wp_apply (hStats st.tx) $$ [$Hdone] as %s3 -
    wp_apply hSeconds as %f3 -
    wp_apply Hs3
    wp_apply time.wp_Since as %d -
    wp_apply hSeconds as %f4 -
    wp_apply Hs4
    wp_apply (wp_commitsAdd b (W64 1)) $$ [$Hmi] as %nc -
    icases Hr with (⟨%Herr, Hown, Hwr⟩ | %Herr)
    · subst Herr
      wp_auto
      cases stop
      · try wp_auto
        wp_apply (hBegin γ.db b db st.S true) $$ [$Hmu $Hown Hwr] as %tx' ⟨Hmu, Hown, #Htxdb', Hwtx'⟩
        · iframe #
          simp only [↓reduceIte]
          iexact Hwr
        iapply HΦ
        iframe Hmu
        iright
        iframe Hown Hpend
        isplitr
        · ipureintro; exact Hnot
        iexists _
        iframe Htxf
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        iframe #
      · try wp_auto
        iapply HΦ
        iframe Hmu
        iright
        iframe Hown Hpend
        isplitr
        · ipureintro; exact Hnot
        iexists _
        iframe Htxf
        simp only [↓reduceIte]
        itrivial
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

end proof

end EtcdGrove
end Perennial
