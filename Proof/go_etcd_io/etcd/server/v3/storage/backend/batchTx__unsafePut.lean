/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__unsafePut.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__unsafePut
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Stack
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__Put

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
`_kv` spec `Tx.Bucket_kvw`). -/
private theorem bbolt.kvGlue_Tx__Bucket_kvw (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; ownWTxG tx γ D S G ∗ name ↦*{dq} n ∗
      ((⌜S.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜S.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ wBkt tx γ b n (G n))) }} := by
  intro tx γ D S G name n dq
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, Hn⟩ HΦ
    have h' := h tx γ 1 (wView D S G) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hn] as %b ⟨Hl, Hn, Hr⟩
    · ipureintro; first | trivial | exact fun _ => rfl
    iapply HΦ; iframe Hl Hn
    iexact Hr

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Bucket.Put_kv`). -/
private theorem bbolt.kvGlue_Bucket__Put_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Put.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData) (key value : GoSlice) (kb vb : GoString) (dk : DFrac),
  G n = g → S.lookup n = some m → 0 < kb.length → kb.length ≤ backend.maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g ∗ key ↦*{dk} kb ∗ value ↦*□ vb }}
    (App (App (Val (b @!! go.GoType.PointerType go_etcd_io.bbolt.Bucket.ty @!! go!"Put")) (Val #key)) (Val #value))
  {{ (err : GoInterface), RET #err; key ↦*{dk} kb ∗
      ((⌜kb.length + vb.length ≤ bbolt.bboltEntryMax ∧ err = GoInterface.nil⌝ ∗
          ownWTxG tx γ D (S.insert n (m.insert kb vb)) G) ∨
       (⌜bbolt.bboltEntryMax < kb.length + vb.length ∧ err ≠ GoInterface.nil⌝ ∗ ownWTxG tx γ D S G)) }} := by
  intro tx γ D S G b n g m key value kb vb dk hg hm hk0 hk1
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.ownWTxG, backend.txLive, backend.wBkt, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownWTxG, backend.txLive, backend.wBkt, onFs_some hfs]
    iintro %Φ ⟨-, Hl, #Hb, Hk, #Hv⟩ HΦ
    subst hg
    have h' := h tx γ (wView D S G) b n m key value kb vb dk
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, wView_setBkt] at h'
    wp_apply h' $$ [$Hl $Hb $Hk $Hv] as %err ⟨Hk, Hres⟩
    · ipureintro; exact ⟨trivial, hm⟩
    by_cases hbig : bbolt.bboltEntryMax < kb.length + vb.length
    · rw [if_pos (Or.inr (Or.inr hbig))]
      icases Hres with ⟨%He, Hl⟩
      iapply HΦ; iframe Hk; iright; iframe Hl; ipureintro; exact ⟨hbig, He⟩
    have hne : ¬ (kb.length = 0 ∨ bbolt.maxKeySize < kb.length ∨ bbolt.bboltEntryMax < kb.length + vb.length) := by
      unfold backend.maxKeySize at hk1; unfold bbolt.maxKeySize; omega
    rw [if_neg hne]
    icases Hres with ⟨%He, Hl⟩
    iapply HΦ; iframe Hk; ileft; iframe Hl; ipureintro; exact ⟨by omega, He⟩

theorem backend.batchTx.unsafePut.wp_proof
    (hBucket : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hStack : zap.Stack.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hPut : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Put.spec (GF := GF) (hG := hG))
    (_hError : zap.Error.spec (GF := GF) (hG := hG)) :
    backend.batchTx.unsafePut.spec (GF := GF) (hG := hG) := by
  replace hBucket := bbolt.kvGlue_Tx__Bucket_kvw hBucket
  replace hPut := bbolt.kvGlue_Bucket__Put_kv hPut
  intro γ P W Pk b t st bk bi key value kb vb dk seq Hk0 Hk1
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey, #Hval⟩
  icases isBackend_bt γ P W Pk b t $$ [Hb Ht] with
    ⟨%db, %lg, %h, #Hbe, #Hlg, #Hlgn, #-, #-, #-, #-, #-, %HP⟩
  · iframe #
  unfold btW
  icases Hw with ⟨Htx, Hpend, ⟨%G, Hwtx⟩⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %Hbo, #-, #HName, #-⟩
  subst Hbo
  wp_auto
  wp_apply HName as %ns #Hns
  wp_apply (hBucket st.tx γ.db st.C st.S G ns bi.name DFrac.discard) $$ [$Hwtx $Hns] as %bkt ⟨Hwtx, -, Hbr⟩
  icases Hbr with (%Hn | ⟨%Hn, #Hwb⟩)
  · obtain ⟨Hn, Hnil⟩ := Hn
    subst Hnil
    wp_auto
    wp_apply hStringer as %f1 -
    wp_apply hStack as %f2 -
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply hFatal lg $$ [] as %v Hf
    · iexact Hlgn
    iexfalso
    iexact Hf
  obtain ⟨Hn, Hnn⟩ := Hn
  obtain ⟨m, Hm⟩ : ∃ m, st.S.lookup bi.name = some m := Option.ne_none_iff_exists'.mp Hn
  wp_if_destruct
  · exact absurd rfl Hnn
  wp_join with [Hwtx bucket]
  · icases ownWTxG_fill st.tx bkt γ.db st.C st.S G bi.name (G bi.name) $$ [$Hwtx $Hwb] with ⟨%f, Hf, Hback⟩
    wp_auto
    ispecialize Hback $$ %_ %(by decide : ¬ bbolt.float64IsNaN (W64 4606281698874543309)) Hf
    wp_join_done
  wp_apply (hPut st.tx γ.db st.C st.S G bkt bi.name (G bi.name) m key value kb vb dk rfl Hm Hk0 Hk1)
    $$ [$Hwtx $Hwb $Hkey $Hval] as %err ⟨Hkey, Hres⟩
  icases Hres with (⟨%Hok, Hwtx⟩ | ⟨%Hbig, -⟩)
  rotate_left
  · -- an entry above bbolt's bound: `Put` refuses it and the backend exits (`lg.Fatal`)
    obtain ⟨-, Hne⟩ := Hbig
    obtain ⟨eo, rfl⟩ : ∃ eo, err = GoInterface.ok eo := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok eo => exact ⟨eo, rfl⟩
    wp_auto
    wp_apply hStringer as %f1 -
    wp_apply _hError as %f2 -
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    try iintro %_ ⟨_, -⟩
    try wp_auto
    wp_apply hFatal lg $$ [] as %v Hf
    · iexact Hlgn
    iexfalso
    iexact Hf
  obtain ⟨Hfit, rfl⟩ := Hok
  (try wp_auto)
  iapply HΦ
  isplitr
  · ipureintro; exact Hfit
  unfold BSess.put bktOf
  rw [Hm]
  iframe
  iexists G
  iframe

end proof

end EtcdGrove
end Perennial
