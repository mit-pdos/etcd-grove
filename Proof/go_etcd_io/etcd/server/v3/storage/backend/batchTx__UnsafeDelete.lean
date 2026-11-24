/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeDelete.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDelete
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Stack
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__Delete

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
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
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
`_kv` spec `Bucket.Delete_kv`). -/
private theorem bbolt.kvGlue_Bucket__Delete_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Delete.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : backend.BktData) (key : GoSlice) (kb : GoString) (dk : DFrac) (own : Bool),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx γ b n g ∗
      (if own then key ↦*{dk} kb else backend.txBytes tx γ key kb) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.bbolt.Bucket.ty @!! go!"Delete")) (Val #key))
  {{ RET #GoInterface.nil; ownWTxG tx γ D (S.insert n (m.delete kb)) G ∗
      (if own then key ↦*{dk} kb else backend.txBytes tx γ key kb) }} := by
  intro tx γ D S G b n g m key kb dk own hg hm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, #Hb, Hk⟩ HΦ
    subst hg
    have h' := h tx γ (wView D S G) b n m key kb dk own
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hb $Hk] as ⟨Hl, Hk⟩
    · ipureintro; exact ⟨trivial, hm⟩
    iapply HΦ; iframe

theorem backend.batchTx.UnsafeDelete.wp_proof
    (hBucket : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hStack : zap.Stack.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG))
    (hDelete : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Delete.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeDelete.spec (GF := GF) (hG := hG) := by
  replace hBucket := bbolt.kvGlue_Tx__Bucket_kvw hBucket
  replace hDelete := bbolt.kvGlue_Bucket__Delete_kv hDelete
  intro γ P W Pk b t st bk bi key kb dk own
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk, Hkey⟩
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
  -- the key, the caller's own slice or one of the session's transaction (`Delete_kv`'s `own`)
  have hDel := hDelete st.tx γ.db st.C st.S G bkt bi.name (G bi.name) m key kb dk own rfl Hm
  wp_apply hDel $$ [$Hwtx $Hwb $Hkey] as ⟨Hwtx, Hkey⟩
  iapply HΦ
  unfold BSess.del bktOf
  rw [Hm]
  iframe
  iexists G
  iframe

end proof

end EtcdGrove
end Perennial
