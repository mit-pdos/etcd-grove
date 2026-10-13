/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__commit.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__commit
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__begin
public import Spec.go_etcd_io.bbolt.Tx__Commit_kv
public import Spec.go_etcd_io.bbolt.Tx__Stats_kv
public import Spec.time.Duration__Seconds
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
variable [go_etcd_io.bbolt.Assumptions] [go_uber_org.zap.Assumptions] [_root_.Perennial.time.Assumptions]

theorem backend.batchTx.commit.wp_proof
    (hCommit : bbolt.Tx.Commit_kv.spec (GF := GF) (hG := hG))
    (hStats : bbolt.Tx.Stats_kv.spec (GF := GF) (hG := hG))
    (hSeconds : time.Duration.Seconds.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hBegin : backend.backend.begin.spec (GF := GF) (hG := hG)) :
    backend.batchTx.commit.spec (GF := GF) (hG := hG) := by
  intro γ P WR b t db st stop
  wp_start as ⟨#Hb, #Ht, Hw, Hown, #Htxdb, Hmu⟩
  icases isBackend_bt γ P WR b t $$ [Hb Ht] with
    ⟨%db0, %lg, %h, #Hbe, #Hlg, %Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  icases isBackend_b γ P WR b $$ Hb with ⟨%t', %rt, %db1, %lg', #-, #-, #-, %-, #Hmi, #-⟩
  ihave Hi : (backendInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨⟨%h1, #Hg1, #Hs1⟩, ⟨%h2, #Hg2, #Hs2⟩, ⟨%h3, #Hg3, #Hs3⟩, ⟨%h4, #Hg4, #Hs4⟩⟩
  unfold histSpec
  unfold btW
  icases Hw with ⟨Htxf, Hpend, Hwtx⟩
  icases ownWTx_live st.tx γ.db st.C st.S $$ Hwtx with ⟨Hlive, Hback⟩
  ihave %Hnn := txLive_nonnull st.tx 1 $$ Hlive
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
        · ipureintro; exact Hlgn
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
        wp_apply (hBegin γ P WR b db st.S true) $$ [$Hmu $Hown Hwr] as %tx' ⟨Hmu, Hown, #Htxdb', Hwtx'⟩
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
        · ipureintro; exact Hlgn
        iexfalso
        iexact Hf
      · exact absurd rfl Herr

end proof

end EtcdGrove
end Perennial
