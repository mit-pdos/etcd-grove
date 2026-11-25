/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeRange.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeRange
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Stack
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__Cursor

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
`_kv` spec `Bucket.Cursor_kvw`). -/
private theorem bbolt.kvGlue_Bucket__Cursor_kvw (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Cursor.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.bbolt.Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx γ c (wView D S G) (backend.bktEnts m) none ∗ ownWTxG tx γ D S G }} := by
  intro tx γ D S G b n g m hg hm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, #Hb⟩ HΦ
    subst hg
    have h' := h tx γ 1 (wView D S G) b n m
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hb] as %c ⟨Hl, Hc⟩
    · ipureintro; exact hm
    iapply HΦ; iframe

theorem backend.batchTx.UnsafeRange.wp_proof
    (hBucket : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hStack : zap.Stack.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hCursor : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Cursor.spec (GF := GF) (hG := hG))
    (hRange : backend.unsafeRange.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeRange.spec (GF := GF) (hG := hG) := by
  replace hBucket := bbolt.kvGlue_Tx__Bucket_kvw hBucket
  replace hCursor := bbolt.kvGlue_Bucket__Cursor_kvw hCursor
  intro γ P W Pk b t st bk bi key endKey kb eb dk de limit
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey, HendKey⟩
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
  wp_apply (hCursor st.tx γ.db st.C st.S G bkt bi.name (G bi.name) m rfl Hm) $$ [$Hwtx $Hwb]
    as %c ⟨Hcur, Hwtx⟩
  iunfold ownWTxG at Hwtx
  wp_apply (hRange st.tx c γ.db (wView st.C st.S G) (bktEnts m) none 1 key endKey kb eb dk de limit)
    $$ [$Hcur $Hwtx $Hkey $HendKey] as %keys %vals ⟨⟨%pos', -⟩, Hwtx, Hkey, HendKey, Hout⟩
  iapply HΦ
  unfold bktOf
  rw [Hm]
  iframe
  iexists G
  iunfold ownWTxG
  iexact Hwtx

end proof

end EtcdGrove
end Perennial
