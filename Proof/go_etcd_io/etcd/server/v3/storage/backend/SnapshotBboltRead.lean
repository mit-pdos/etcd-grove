/- Read-transaction bucket lookup and cursor construction for backend readers. -/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Spec.go_etcd_io.bbolt.Bucket__Cursor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Tx.Bucket_kvr`). -/
theorem bbolt.kvGlue_Tx__Bucket_kvr (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Bucket.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ txLive tx γ q (bbolt.TxView.ro D) ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; txLive tx γ q (bbolt.TxView.ro D) ∗ name ↦*{dq} n ∗
      ((⌜D.lookup n = none ∧ b = Loc.null⌝) ∨
       (∃ m : backend.BktData, ⌜D.lookup n = some m ∧ b ≠ Loc.null⌝ ∗ wBkt tx γ b n 0)) }} := by
  intro tx γ q D name n dq
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, Hn⟩ HΦ
    have h' := h tx γ q (TxView.ro D) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hn] as %b ⟨Hl, Hn, Hr⟩
    · ipureintro; intro h'; cases h'
    iapply HΦ; iframe Hl Hn
    icases Hr with (%Hr | ⟨%Hr, #Hb⟩)
    · ileft; ipureintro; exact Hr
    · iright
      obtain ⟨hn, hb⟩ := Hr
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hn
      iexists m
      isplitr
      · ipureintro; exact ⟨hm, hb⟩
      · iexact Hb

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- (S3e) bbolt's canonical spec in the backend's vocabulary, at `theFs` (until then the
`_kv` spec `Bucket.Cursor_kvr`). -/
theorem bbolt.kvGlue_Bucket__Cursor_kvr (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Bucket.Cursor.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data) (b : Loc) (n : GoString) (m : backend.BktData),
  D.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ wBkt tx γ b n 0 ∗ txLive tx γ q (bbolt.TxView.ro D) }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.bbolt.Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx γ c (bbolt.TxView.ro D) (backend.bktEnts m) none ∗ txLive tx γ q (bbolt.TxView.ro D) }} := by
  intro tx γ q D b n m hm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨-, H⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hb, Hl⟩ HΦ
    have h' := h tx γ q (TxView.ro D) b n m
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hb] as %c ⟨Hl, Hc⟩
    · ipureintro; exact hm
    iapply HΦ; iframe

end proof
end EtcdGrove
end Perennial
