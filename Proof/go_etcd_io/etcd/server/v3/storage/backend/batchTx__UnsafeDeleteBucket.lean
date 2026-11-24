/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/batchTx__UnsafeDeleteBucket.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTx__UnsafeDeleteBucket
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__DeleteBucket

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
`_kv` spec `Tx.DeleteBucket_kv`). -/
private theorem bbolt.kvGlue_Tx__DeleteBucket_kv (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.DeleteBucket.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      ((⌜S.lookup n = none⌝ ∗ ownWTxG tx γ D S G ∗
        globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err) ∨
       (⌜n = [] ∧ S.lookup n = none⌝ ∗ ownWTxG tx γ D S G ∗
        globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue ↦□ err) ∨
       (⌜S.lookup n ≠ none ∧ err = GoInterface.nil⌝ ∗
        ownWTxG tx γ D (S.delete n) (fun x => if x = n then G n + 1 else G x))) }} := by
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
    have h' := h tx γ (wView D S G) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hn] as %err ⟨Hn, Hr⟩
    all_goals try (ipureintro; first | trivial | rfl)
    iapply HΦ; iframe Hn
    icases Hr with (⟨%Hr, Hl, #He⟩ | ⟨%Hr, Hl, #He⟩ | ⟨%Hr, Hl⟩)
    · ileft; iframe Hl; isplitr; · ipureintro; exact Hr
      iexact He
    · iright; ileft; iframe Hl; isplitr; · ipureintro; exact Hr
      iexact He
    · iright; iright; isplitr; · ipureintro; exact Hr
      iexact Hl

theorem backend.batchTx.UnsafeDeleteBucket.wp_proof
    (hDelBkt : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.DeleteBucket.spec (GF := GF) (hG := hG))
    (hStringer : zap.Stringer.spec (GF := GF) (hG := hG))
    (hError : zap.Error.spec (GF := GF) (hG := hG))
    (hFatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    backend.batchTx.UnsafeDeleteBucket.spec (GF := GF) (hG := hG) := by
  replace hDelBkt := bbolt.kvGlue_Tx__DeleteBucket_kv hDelBkt
  intro γ P W Pk b t st bk bi Hne
  wp_start as ⟨#Hb, #Ht, Hw, #Hbk⟩
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  icases Hei with ⟨%e, #He, %Hel, -⟩
  obtain ⟨Hptr, Hleaf, HIs⟩ := Hel
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
  wp_apply (hDelBkt st.tx γ.db st.C st.S G ns bi.name DFrac.discard) $$ [$Hwtx $Hns]
    as %err ⟨-, Hr⟩
  icases Hr with (⟨%Hn, Hwtx, #Herr⟩ | ⟨%Hn, -, -⟩ | ⟨%Hn, Hwtx⟩)
  rotate_left
  · exact absurd Hn.1 Hne
  rotate_right
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
    simp only [Option.getD_some]
    iexists G
    iexact Hwtx
  · obtain ⟨Hn, Herr⟩ := Hn
    subst Herr
    wp_auto
    iapply HΦ
    iframe
    iexists (fun x => if x = bi.name then G bi.name + 1 else G x)
    iframe

end proof

end EtcdGrove
end Perennial
