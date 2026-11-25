/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeCreateBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeCreateBucket
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists

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
`_kv` spec `Tx.CreateBucketIfNotExists_kv`). -/
private theorem bbolt.kvGlue_Tx__CreateBucketIfNotExists_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.CreateBucketIfNotExists.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  0 < n.length → n.length ≤ backend.maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"CreateBucketIfNotExists")) (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); ⌜err = GoInterface.nil⌝ ∗
      ownWTxG tx γ D (if S.lookup n = none then S.insert n ∅ else S) G ∗ wBkt tx γ b n (G n) ∗
      name ↦*{dq} n }} := by
  intro tx γ D S G name n dq hn0 hnm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, Hn⟩ HΦ
    have h' := h tx γ (wView D S G) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    have hc : ¬ n.length = 0 := by omega
    simp only [if_neg hc] at h'
    wp_apply h' $$ [$Hl $Hn] as %b %err ⟨Hn, Hr⟩
    · ipureintro; exact ⟨trivial, hnm⟩
    icases Hr with ⟨%He, #Hb, Hl⟩
    iapply HΦ
    iframe Hn
    isplitr; · ipureintro; exact He
    isplitl [Hl]
    · rw [show wView D (if S.lookup n = none then S.insert n ∅ else S) G =
          (if S.lookup n = none then wView D (S.insert n ∅) G else wView D S G) by split <;> rfl]
      iexact Hl
    · iexact Hb

theorem backend.batchTx.UnsafeCreateBucket.wp_proof
    (hCreate : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.CreateBucketIfNotExists.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeCreateBucket.spec (GF := GF) (hG := hG) := by
  replace hCreate := bbolt.kvGlue_Tx__CreateBucketIfNotExists_kv hCreate
  intro γ P W Pk b t st bk bi Hn0 Hn1
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk⟩
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
  wp_apply (hCreate st.tx γ.db st.C st.S G ns bi.name DFrac.discard Hn0 Hn1) $$ [$Hwtx $Hns]
    as %bkt %err ⟨%Herr, Hwtx, -, -⟩
  subst Herr
  wp_auto
  iapply HΦ
  iframe
  iexists G
  iframe

end proof

end EtcdGrove
end Perennial
